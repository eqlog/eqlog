use crate::ast_v1::*;
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
            Application { args, .. } => {
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
            Application { func, args } => {
                let args: Vec<FlatTerm> = args
                    .iter()
                    .copied()
                    .map(|arg| self.flat_names[arg].unwrap())
                    .chain(once(name))
                    .collect();
                out_atoms.push(FlatAtom::Relation(func.clone(), args));
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

                if self.added[lhs] && self.added[rhs] {
                    let lhs_name = self.flat_names[lhs].unwrap();
                    let rhs_name = self.flat_names[rhs].unwrap();
                    // Both terms have already been added. If they do not have the same flat name,
                    // then we must emit an explicit equality atom. Otherwise, nothing needs to be
                    // done.
                    if lhs_name != rhs_name {
                        out_atoms.push(FlatAtom::Equal(lhs_name, rhs_name));
                        self.flat_names.union(lhs, rhs);
                    }
                } else {
                    // At least one term has not been added up until now. We unify the (future)
                    // flat names of the two terms before emitting their structure. This way, no
                    // explicit equality atom is necessary.
                    self.flat_names.union(lhs, rhs);
                    for tm in atom.iter_subterms(&self.universe) {
                        self.emit_term_structure(tm, out_atoms);
                    }
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
        .filter_map(|tm| {
            term_map
                .get(&tm)
                .map(|flat_tm| (*flat_tm, sorts[tm].to_string()))
        })
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
        TermData::Application { args, .. } => args,
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
