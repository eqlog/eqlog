use crate::ast::*;
use crate::flat_ast::*;
use crate::unification::*;
use std::collections::BTreeMap;
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
    term_map: BTreeMap<Term, FlatTerm>,
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
            term_map: BTreeMap::new(),
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
            let flat_term = self.flat_names[term].unwrap();
            if let Some(prev_flat_tm) = self.term_map.insert(term, flat_term) {
                debug_assert_eq!(prev_flat_tm, flat_term);
            }
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
        self.term_map.insert(term, name);

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

#[derive(Clone, Debug)]
pub struct SequentFlattening {
    pub term_map: BTreeMap<Term, FlatTerm>,
    pub sequent: FlatSequent,
    pub sorts: BTreeMap<FlatTerm, String>,
}

fn flatten_implication<'a, 'b>(
    universe: &TermUniverse,
    premise: impl Clone + IntoIterator<Item = &'a Atom>,
    conclusion: impl IntoIterator<Item = &'b Atom>,
    sorts: &TermMap<String>,
) -> SequentFlattening {
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

    let term_map = emitter.term_map;

    let flat_sorts: BTreeMap<FlatTerm, String> = universe
        .iter_terms()
        .map(|tm| (*term_map.get(&tm).unwrap(), sorts[tm].to_string()))
        .collect();

    SequentFlattening {
        term_map,
        sequent: flat_sequent,
        sorts: flat_sorts,
    }
}

fn flatten_reduction<'a>(
    universe: &TermUniverse,
    premise: impl Clone + IntoIterator<Item = &'a Atom>,
    from: Term,
    to: Term,
    sorts: &TermMap<String>,
) -> SequentFlattening {
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

pub fn flatten_sequent(sequent: &Sequent, sorts: &TermMap<String>) -> Vec<SequentFlattening> {
    use SequentData::*;
    let universe = &sequent.universe;
    match &sequent.data {
        Implication {
            premise,
            conclusion,
        } => {
            vec![flatten_implication(
                universe,
                premise.iter(),
                conclusion.iter(),
                sorts,
            )]
        }
        Reduction { premise, from, to } => {
            vec![flatten_reduction(
                universe,
                premise.iter(),
                *from,
                *to,
                sorts,
            )]
        }
        Bireduction { premise, lhs, rhs } => {
            let left_to_right = flatten_reduction(universe, premise.iter(), *lhs, *rhs, sorts);
            let right_to_left = flatten_reduction(universe, premise.iter(), *rhs, *lhs, sorts);
            return vec![left_to_right, right_to_left];
        }
    }
}

#[derive(Clone, Debug)]
pub struct QueryFlattening {
    pub term_map: BTreeMap<Term, FlatTerm>,
    pub query: FlatQuery,
    pub sorts: BTreeMap<FlatTerm, String>,
}

pub fn flatten_query(query: &UserQuery, sorts: &TermMap<String>) -> QueryFlattening {
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

    let term_map = emitter.term_map;

    let flat_sorts: BTreeMap<FlatTerm, String> = universe
        .iter_terms()
        .map(|tm| (*term_map.get(&tm).unwrap(), sorts[tm].to_string()))
        .collect();

    QueryFlattening {
        query: flat_query,
        term_map,
        sorts: flat_sorts,
    }
}
