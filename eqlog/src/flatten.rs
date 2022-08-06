use crate::ast::*;
use crate::flat_ast::*;
use crate::unification::*;
use std::iter::once;

// Various `TermUnification` types for bookkeeping during emission.

// `NameUnification` keeps track of flat names assigned to terms (if any).
struct NameMerge {}
impl MergeFn<Option<FlatTerm>> for NameMerge {
    fn merge(&mut self, lhs: Option<FlatTerm>, rhs: Option<FlatTerm>) -> Option<FlatTerm> {
        match lhs {
            Some(name) => Some(name),
            None => rhs,
        }
    }
}
type NameUnification<'a> = TermUnification<'a, Option<FlatTerm>, NameMerge>;

// `IsAddedUnification` keeps track of whether a term was already processed during emission.
struct IsAddedMerge {}
impl MergeFn<bool> for IsAddedMerge {
    fn merge(&mut self, lhs: bool, rhs: bool) -> bool {
        lhs || rhs
    }
}
type IsAddedUnification<'a> = TermUnification<'a, bool, IsAddedMerge>;

// `IsConstraindUnification` keeps track of whether a term is constrained by some relation in the
// premise. For example, in
//
//     y = f(x) & z : Foo => ...
//
// y, x and f(x) are constrained, whereas z is unconstrained.
struct IsConstrainedMerge {}
impl MergeFn<bool> for IsConstrainedMerge {
    fn merge(&mut self, lhs: bool, rhs: bool) -> bool {
        lhs || rhs
    }
}
type IsConstrainedUnification<'a> = TermUnification<'a, bool, IsConstrainedMerge>;

struct Emitter<'a> {
    universe: &'a TermUniverse,
    flat_names: NameUnification<'a>,
    name_num: FlatTerm,
    added: IsAddedUnification<'a>,
    constrained: IsConstrainedUnification<'a>,
    sorts: &'a TermMap<String>,
}

impl<'a> Emitter<'a> {
    fn new(universe: &'a TermUniverse, sorts: &'a TermMap<String>) -> Self {
        let mut flat_names =
            NameUnification::new(universe, vec![None; universe.len()], NameMerge {});
        flat_names.congruence_closure();
        let mut added =
            IsAddedUnification::new(universe, vec![false; universe.len()], IsAddedMerge {});
        added.congruence_closure();
        let mut constrained = IsConstrainedUnification::new(
            universe,
            vec![false; universe.len()],
            IsConstrainedMerge {},
        );
        constrained.congruence_closure();

        Emitter {
            universe,
            flat_names,
            name_num: FlatTerm(0),
            added,
            constrained,
            sorts,
        }
    }

    // Mark terms as constrained based on the structure of a given `term` (but not based on
    // subterms of `term`).
    fn setup_premise_term(&mut self, term: Term) {
        use TermData::*;
        match self.universe.data(term) {
            Variable(_) | Wildcard => (),
            Application(_, args) => {
                for arg in args.iter().copied() {
                    self.constrained[arg] = true;
                }
                self.constrained[term] = true;
            }
        }
        self.constrained.congruence_closure();
    }

    // Mark terms as constrained based on a given `atom` (but not based on subterms of `atom`).
    fn setup_premise_atom(&mut self, atom: &Atom) {
        use AtomData::*;
        match &atom.data {
            Equal(lhs, rhs) => {
                self.constrained.union(*lhs, *rhs);
                // Unless both terms are already added (e.g. because they are arguments of a
                // query), we can merge their names so that we don't have to explicitly generate a
                // `FlatAtom::Equals` for them.
                if !(self.added[*lhs] && self.added[*rhs]) {
                    self.flat_names.union(*lhs, *rhs);
                }
            }
            Defined(_, _) => (),
            Predicate(_, args) => {
                for arg in args.iter().copied() {
                    self.constrained[arg] = true;
                }
            }
        }
        self.constrained.congruence_closure();
        self.flat_names.congruence_closure();
    }

    // Emit a flat atom corresponding to the structure of a term, if any. All subterms of `term`
    // must already be added. If `term` was already added, nothing is emitted, and similarly for
    // constrained variables/wildcards.
    fn emit_term_structure(&mut self, term: Term, out_atoms: &mut Vec<FlatAtom>) {
        if self.added[term] {
            return;
        }
        self.added[term] = true;

        let name = match self.flat_names[term] {
            Some(name) => name,
            None => {
                let name = self.name_num;
                self.flat_names[term] = Some(name);
                self.name_num = FlatTerm(self.name_num.0 + 1);
                name
            }
        };

        use TermData::*;
        match self.universe.data(term) {
            Variable(_) | Wildcard => {
                if !self.constrained[term] {
                    out_atoms.push(FlatAtom::Unconstrained(name, self.sorts[term].clone()));
                }
            }
            Application(func_name, args) => {
                let args: Vec<FlatTerm> = args
                    .iter()
                    .copied()
                    .map(|arg| self.flat_names[arg].unwrap())
                    .chain(once(name))
                    .collect();
                out_atoms.push(FlatAtom::Relation(func_name.clone(), args));
            }
        };
    }

    // Emit flat atoms corresponding to an atom and its subterms.
    fn emit_atom(&mut self, atom: &Atom, out_atoms: &mut Vec<FlatAtom>) {
        use AtomData::*;
        match &atom.data {
            Equal(lhs, rhs) => {
                let lhs = *lhs;
                let rhs = *rhs;

                // Save names of lhs and rhs in case both names already exist and are not equal.
                // If that is the case, we must explicitly emit a `FlatAtom::Equal` later. If at
                // least one name did not exist or both names existed, we unify the names of `lhs`
                // and `rhs` *before* adding `lhs` and `rhs` to save the `FlatAtom::Equal`.
                let emit_equal_names: Option<(FlatTerm, FlatTerm)> =
                    match (self.flat_names[lhs], self.flat_names[rhs]) {
                        (Some(lhs_name), Some(rhs_name)) if lhs_name != rhs_name => {
                            Some((lhs_name, rhs_name))
                        }
                        _ => None,
                    };

                // Unify the names of lhs and rhs before emitting term structure. In case at least
                // one of the names did not exist already, we can then omit adding an equality.
                self.flat_names.union(lhs, rhs);
                for tm in atom.iter_subterms(&self.universe) {
                    self.emit_term_structure(tm, out_atoms);
                }

                // If both lhs and rhs have already had names, we must explictly equalize them now.
                if let Some((lhs_name, rhs_name)) = emit_equal_names {
                    out_atoms.push(FlatAtom::Equal(lhs_name, rhs_name));
                }

                self.added.union(lhs, rhs);
                self.added.congruence_closure();
                self.flat_names.congruence_closure();
            }
            Defined(_, _) => {
                for tm in atom.iter_subterms(&self.universe) {
                    self.emit_term_structure(tm, out_atoms);
                }
            }
            Predicate(pred, args) => {
                for tm in atom.iter_subterms(&self.universe) {
                    self.emit_term_structure(tm, out_atoms);
                }
                let args = args
                    .iter()
                    .copied()
                    .map(|arg| self.flat_names[arg].unwrap())
                    .collect();
                out_atoms.push(FlatAtom::Relation(pred.clone(), args));
            }
        }
    }
}

fn flatten_implication<'a, 'b>(
    universe: &TermUniverse,
    premise: impl Clone + IntoIterator<Item = &'a Atom>,
    conclusion: impl IntoIterator<Item = &'b Atom>,
    sorts: &TermMap<String>,
) -> FlatSequent {
    let mut emitter = Emitter::new(&universe, sorts);

    for atom in premise.clone() {
        for tm in atom.iter_subterms(universe) {
            emitter.setup_premise_term(tm);
        }
        emitter.setup_premise_atom(&atom);
    }

    let mut flat_premise: Vec<FlatAtom> = Vec::new();
    for atom in premise {
        emitter.emit_atom(&atom, &mut flat_premise);
    }

    let mut flat_conclusion: Vec<FlatAtom> = Vec::new();
    for atom in conclusion {
        emitter.emit_atom(&atom, &mut flat_conclusion);
    }

    let flat_sequent = FlatSequent {
        premise: flat_premise,
        conclusion: flat_conclusion,
    };
    #[cfg(debug_assertions)]
    flat_sequent.check();
    flat_sequent
}

fn flatten_reduction<'a>(
    universe: &TermUniverse,
    premise: impl Clone + IntoIterator<Item = &'a Atom>,
    from: Term,
    to: Term,
    sorts: &TermMap<String>,
) -> FlatSequent {
    let from_args = match universe.data(from) {
        TermData::Application(_, args) => args,
        // Must be checked earlier:
        _ => panic!("Reduction from a variable"),
    };
    let synthetic_premise: Vec<Atom> = premise
        .into_iter()
        .cloned()
        .chain(from_args.iter().copied().chain(once(to)).map(|tm| Atom {
            data: AtomData::Defined(tm, None),
            location: None,
        }))
        .collect();

    let eq = Atom {
        data: AtomData::Equal(from, to),
        location: None,
    };
    let synthetic_conclusion = once(&eq);

    let result = flatten_implication(
        universe,
        synthetic_premise.iter(),
        synthetic_conclusion,
        sorts,
    );
    result
}

pub fn flatten_sequent(sequent: &Sequent, sorts: &TermMap<String>) -> FlatSequent {
    use SequentData::*;
    let universe = &sequent.universe;
    match &sequent.data {
        Implication {
            premise,
            conclusion,
        } => flatten_implication(universe, premise.iter(), conclusion.iter(), sorts),
        Reduction { premise, from, to } => {
            flatten_reduction(universe, premise.iter(), *from, *to, sorts)
        }
    }
}

pub fn flatten_query(query: &UserQuery, sorts: &TermMap<String>) -> FlatQuery {
    let universe = &query.universe;

    let mut emitter = Emitter::new(&query.universe, sorts);

    let mut inputs: Vec<(FlatTerm, String)> = Vec::new();
    let mut flat_atoms: Vec<FlatAtom> = Vec::new();

    for QueryArgument { variable, .. } in query.arguments.iter() {
        emitter.constrained[*variable] = true;
        emitter.emit_term_structure(*variable, &mut flat_atoms);
        assert!(flat_atoms.is_empty());
        let flat_variable = emitter.flat_names[*variable].unwrap();
        let sort = sorts[*variable].clone();
        inputs.push((flat_variable, sort));
    }

    for tm in query.result.iter_subterms(universe) {
        emitter.setup_premise_term(tm);
    }

    if let Some(where_formula) = &query.where_formula {
        for atom in where_formula.iter() {
            for tm in atom.iter_subterms(universe) {
                emitter.setup_premise_term(tm);
            }
            emitter.setup_premise_atom(atom);
        }
    }

    for tm in query.result.iter_subterms(universe) {
        emitter.emit_term_structure(tm, &mut flat_atoms);
    }

    if let Some(where_formula) = &query.where_formula {
        for atom in where_formula.iter() {
            emitter.emit_atom(atom, &mut flat_atoms);
        }
    }

    let output = match &query.result {
        QueryResult::NoResult => FlatQueryOutput::NoOutput,
        QueryResult::SingleResult(tm) => {
            let flat_tm = emitter.flat_names[*tm].unwrap();
            let sort = sorts[*tm].clone();
            FlatQueryOutput::SingleOutput(flat_tm, sort)
        }
        QueryResult::TupleResult(tms) => FlatQueryOutput::TupleOutput(
            tms.iter()
                .map(|tm| {
                    let flat_tm = emitter.flat_names[*tm].unwrap();
                    let sort = sorts[*tm].clone();
                    (flat_tm, sort)
                })
                .collect(),
        ),
    };

    let flat_query = FlatQuery {
        inputs,
        output,
        atoms: flat_atoms,
    };
    #[cfg(debug_assertions)]
    flat_query.check();
    flat_query
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::grammar::SequentParser;

    #[test]
    fn simple_reduction() {
        let src = "comp(h, comp(g, f)) ~> comp(comp(h, g), f)";
        let comp = || "comp".to_string();
        let sequent = SequentParser::new()
            .parse(&mut TermUniverse::new(), src)
            .unwrap();
        let sorts = TermMap::new(vec!["mor".to_string(); sequent.universe.len()]);

        let flat_sequent = flatten_sequent(&sequent, &sorts);

        let h = FlatTerm(0);
        let g = FlatTerm(1);
        let f = FlatTerm(2);
        let gf = FlatTerm(3);
        let hg = FlatTerm(4);
        let hg_f = FlatTerm(5);
        let h_gf = hg_f;

        use FlatAtom::*;
        let premise = vec![
            // comp(g, f)!
            Relation(comp(), vec![g, f, gf]),
            Relation(comp(), vec![h, g, hg]),
            // comp(comp(h, g), f)!
            Relation(comp(), vec![hg, f, hg_f]),
        ];
        assert_eq!(flat_sequent.premise, premise);

        let conclusion = vec![
            // comp(h, comp(g, f)) = comp(comp(h, g), f)
            Relation(comp(), vec![h, gf, h_gf]),
        ];
        assert_eq!(flat_sequent.conclusion, conclusion);
    }

    #[test]
    fn non_surjective_implication() {
        let src =
            "signature(x, f, y) & signature(y, g, z) => comp(g, f)! & signature(x, comp(g, f), z)";
        let mor = || "mor".to_string();
        let obj = || "obj".to_string();
        let signature = || "signature".to_string();
        let comp = || "comp".to_string();

        let sequent = SequentParser::new()
            .parse(&mut TermUniverse::new(), src)
            .unwrap();
        let sorts = TermMap::new(vec![
            obj(), // x
            mor(), // f
            obj(), // y
            obj(), // y
            mor(), // g
            obj(), // z
            mor(), // g
            mor(), // f
            mor(), // comp(g, f)
            obj(), // x
            mor(), // g
            mor(), // f
            mor(), // comp(g, f)
            obj(), // z
        ]);

        let flat_sequent = flatten_sequent(&sequent, &sorts);

        let x = FlatTerm(0);
        let f = FlatTerm(1);
        let y = FlatTerm(2);
        let g = FlatTerm(3);
        let z = FlatTerm(4);
        let gf = FlatTerm(5);

        use FlatAtom::*;
        let premise = vec![
            Relation(signature(), vec![x, f, y]),
            Relation(signature(), vec![y, g, z]),
        ];
        assert_eq!(flat_sequent.premise, premise);

        let conclusion = vec![
            Relation(comp(), vec![g, f, gf]),
            Relation(signature(), vec![x, gf, z]),
        ];
        assert_eq!(flat_sequent.conclusion, conclusion);
    }

    #[test]
    fn surjective_implication() {
        let src = "g = comp(f, id(_)) => f = g";
        let mor = || "mor".to_string();
        let obj = || "obj".to_string();
        let id = || "id".to_string();
        let comp = || "comp".to_string();

        let sequent = SequentParser::new()
            .parse(&mut TermUniverse::new(), src)
            .unwrap();
        let sorts = TermMap::new(vec![
            mor(), // g
            mor(), // f
            obj(), // _
            mor(), // id(_)
            mor(), // comp(f, id(_))
            mor(), // f
            mor(), // g
        ]);

        let flat_sequent = flatten_sequent(&sequent, &sorts);

        let g = FlatTerm(0);
        let f = FlatTerm(1);
        let wc = FlatTerm(2);
        let i = FlatTerm(3);
        let fi = g;

        use FlatAtom::*;
        let premise = vec![
            Relation(id(), vec![wc, i]),
            Relation(comp(), vec![f, i, fi]),
        ];
        assert_eq!(flat_sequent.premise, premise);

        let conclusion = vec![Equal(f, g)];
        assert_eq!(flat_sequent.conclusion, conclusion);
    }

    #[test]
    fn unconstrained_variable() {
        let src = "x!: obj => id(x)! & comp(id(x), id(x)) = id(x)";
        let mor = || "mor".to_string();
        let obj = || "obj".to_string();
        let id = || "id".to_string();
        let comp = || "comp".to_string();

        let sequent = SequentParser::new()
            .parse(&mut TermUniverse::new(), src)
            .unwrap();
        let sorts = TermMap::new(vec![
            obj(), // x
            obj(), // x
            mor(), // id(x)
            obj(), // x
            mor(), // id(x)
            obj(), // x
            mor(), // id(x)
            mor(), // comp(id(x), id(x))
            obj(), // x
            mor(), // id(x)
        ]);

        let flat_sequent = flatten_sequent(&sequent, &sorts);

        let x = FlatTerm(0);
        let i = FlatTerm(1);

        use FlatAtom::*;
        let premise = vec![Unconstrained(x, obj())];
        assert_eq!(flat_sequent.premise, premise);

        let conclusion = vec![Relation(id(), vec![x, i]), Relation(comp(), vec![i, i, i])];
        assert_eq!(flat_sequent.conclusion, conclusion);
    }
}
