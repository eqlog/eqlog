#[cfg(debug_assertions)]
use std::collections::BTreeSet;

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
    pub fn check(&self) {
        let mut occurred: BTreeSet<FlatTerm> = BTreeSet::new();

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

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum FlatQueryOutput {
    NoOutput,
    SingleOutput(FlatTerm, String),
    TupleOutput(Vec<(FlatTerm, String)>),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FlatQuery {
    pub inputs: Vec<(FlatTerm, String)>,
    pub output: FlatQueryOutput,
    pub atoms: Vec<FlatAtom>,
}

#[cfg(debug_assertions)]
impl FlatQuery {
    pub fn check(&self) {
        // Input terms must be pairwise distinct.
        assert_eq!(
            self.inputs
                .iter()
                .map(|(tm, _)| tm)
                .copied()
                .collect::<BTreeSet<FlatTerm>>()
                .len(),
            self.inputs.len()
        );
        let mut occurred: BTreeSet<FlatTerm> = BTreeSet::new();
        for (tm, _) in self.inputs.iter() {
            occurred.insert(*tm);
        }

        for atom in self.atoms.iter() {
            use FlatAtom::*;
            match atom {
                Equal(lhs, rhs) => {
                    assert_ne!(*lhs, *rhs, "FlatAtom::Equal with equal arguments");
                    assert!(occurred.contains(lhs));
                    assert!(occurred.contains(rhs));
                }
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

        match &self.output {
            FlatQueryOutput::NoOutput => (),
            FlatQueryOutput::SingleOutput(tm, _) => {
                assert!(occurred.contains(tm));
            }
            FlatQueryOutput::TupleOutput(tm_sorts) => {
                for (tm, _) in tm_sorts.iter() {
                    assert!(occurred.contains(tm));
                }
            }
        }
    }
}
