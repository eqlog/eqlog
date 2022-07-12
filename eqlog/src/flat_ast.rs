use crate::ast::*;
use crate::unification::*;
use std::collections::HashSet;
use std::iter::once;
use std::mem::swap;

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct FlatTerm(pub usize);

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum FlatAtom {
    Equal(FlatTerm, FlatTerm),
    Relation(String, Vec<FlatTerm>),
    Unconstrained(FlatTerm, String),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FlatSequent {
    pub premise: Vec<FlatAtom>,
    pub conclusion: Vec<FlatAtom>,
}

#[cfg(debug_assertions)]
impl FlatSequent {
    fn check(&self) {
        let mut occurred: HashSet<FlatTerm> = HashSet::new();

        for atom in &self.premise {
            use FlatAtom::*;
            match atom {
                Equal(_, _) => panic!("FlatAtom::Equal in premise"),
                Relation(_, args) => {
                    for arg in args.iter().copied() {
                        occurred.insert(arg);
                    }
                }
                Unconstrained(tm, _) => {
                    occurred.insert(*tm);
                }
            }
        }

        for atom in &self.conclusion {
            use FlatAtom::*;
            match atom {
                Unconstrained(_, _) => panic!("FlatAtom::Unconstrained in conclusion"),
                Relation(_, args) => {
                    if args.len() > 0 {
                        for arg in args[0..args.len() - 1].iter() {
                            assert!(
                                occurred.contains(arg),
                                "All but the last argument of relations must have occured earlier"
                            );
                        }
                    }
                    for arg in args.iter().copied() {
                        occurred.insert(arg);
                    }
                }
                Equal(lhs, rhs) => {
                    assert_ne!(lhs, rhs, "FlatAtom::Equal with equal arguments");
                    occurred.insert(*lhs);
                    occurred.insert(*rhs);
                }
            }
        }
    }
}

struct Emitter<'a, F, G> {
    universe: &'a TermUniverse,
    flat_names: TermUnification<'a, Option<FlatTerm>, F>,
    name_num: FlatTerm,
    structurally_added: TermUnification<'a, bool, G>,
    unconstrained: &'a TermMap<bool>,
    sorts: &'a TermMap<String>,
    flat_atoms: Vec<FlatAtom>,
}

impl<'a, F, G> Emitter<'a, F, G>
where
    F: Fn(Option<FlatTerm>, Option<FlatTerm>) -> Option<FlatTerm>,
    G: Fn(bool, bool) -> bool,
{
    fn emit_term_structure(&mut self, term: Term) {
        if self.structurally_added[term] {
            return;
        }
        self.structurally_added[term] = true;

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
                if self.unconstrained[term] {
                    self.flat_atoms
                        .push(FlatAtom::Unconstrained(name, self.sorts[term].clone()));
                }
            }
            Application(func_name, args) => {
                let args: Vec<FlatTerm> = args
                    .iter()
                    .copied()
                    .map(|arg| self.flat_names[arg].unwrap())
                    .chain(once(name))
                    .collect();
                self.flat_atoms
                    .push(FlatAtom::Relation(func_name.clone(), args));
            }
        };
    }

    fn emit_atom(&mut self, atom: &Atom) {
        use AtomData::*;
        match &atom.data {
            Equal(lhs, rhs) => {
                let lhs = *lhs;
                let rhs = *rhs;

                // Save names of lhs and rhs in case both already exist and are not equal.
                let emit_equal_names: Option<(FlatTerm, FlatTerm)> =
                    match (self.flat_names[lhs], self.flat_names[rhs]) {
                        (Some(lhs_name), Some(rhs_name)) if lhs_name != rhs_name => {
                            Some((lhs_name, rhs_name))
                        }
                        _ => None,
                    };

                self.flat_names.union(lhs, rhs);
                for tm in atom.iter_subterms(&self.universe) {
                    self.emit_term_structure(tm);
                }

                if let Some((lhs_name, rhs_name)) = emit_equal_names {
                    self.flat_atoms.push(FlatAtom::Equal(lhs_name, rhs_name));
                }

                // TODO: Can we savely do this before adding subterms?
                self.structurally_added.union(lhs, rhs);
                self.structurally_added.congruence_closure();
                self.flat_names.congruence_closure();
            }
            Defined(_, _) => {
                for tm in atom.iter_subterms(&self.universe) {
                    self.emit_term_structure(tm);
                }
            }
            Predicate(pred, args) => {
                for tm in atom.iter_subterms(&self.universe) {
                    self.emit_term_structure(tm);
                }
                let args = args
                    .iter()
                    .copied()
                    .map(|arg| self.flat_names[arg].unwrap())
                    .collect();
                self.flat_atoms.push(FlatAtom::Relation(pred.clone(), args));
            }
        }
    }
}

pub fn flatten_sequent(sequent: &Sequent, sorts: &TermMap<String>) -> FlatSequent {
    let universe = &sequent.universe;
    let len = universe.len();

    let mut unconstrained = TermUnification::new(universe, vec![true; len], |lhs, rhs| lhs && rhs);
    let mut flat_names = TermUnification::new(universe, vec![None; len], |lhs, rhs| lhs.or(rhs));

    for tm in sequent
        .premise
        .iter()
        .map(|atom| atom.iter_subterms(universe))
        .flatten()
    {
        use TermData::*;
        match universe.data(tm) {
            Variable(_) | Wildcard => (),
            Application(_, args) => {
                for arg in args.iter().copied() {
                    unconstrained[arg] = false;
                }
                unconstrained[tm] = false;
            }
        }
    }

    for atom in &sequent.premise {
        use AtomData::*;
        match &atom.data {
            Equal(lhs, rhs) => {
                flat_names.union(*lhs, *rhs);
                unconstrained.union(*lhs, *rhs);
            }
            Defined(_, _) => (),
            Predicate(_, args) => {
                for arg in args.iter().copied() {
                    unconstrained[arg] = false;
                }
            }
        }
    }

    unconstrained.congruence_closure();
    let unconstrained = unconstrained.freeze();

    flat_names.congruence_closure();

    let mut structurally_added =
        TermUnification::new(universe, vec![false; len], |lhs, rhs| lhs || rhs);
    structurally_added.congruence_closure();

    let mut emitter = Emitter {
        universe,
        flat_names,
        name_num: FlatTerm(0),
        structurally_added,
        unconstrained: &unconstrained,
        sorts,
        flat_atoms: vec![],
    };

    for atom in &sequent.premise {
        emitter.emit_atom(atom);
    }
    let mut premise: Vec<FlatAtom> = Vec::new();
    swap(&mut premise, &mut emitter.flat_atoms);

    for atom in &sequent.conclusion {
        emitter.emit_atom(atom);
    }
    let conclusion = emitter.flat_atoms;

    let sequent = FlatSequent {
        premise,
        conclusion,
    };
    #[cfg(debug_assertions)]
    sequent.check();
    sequent
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
