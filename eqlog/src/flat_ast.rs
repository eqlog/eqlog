#[cfg(debug_assertions)]
use std::collections::BTreeSet;
use std::fmt::{self, Display, Formatter};

use itertools::Itertools;

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

impl Display for FlatTerm {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "tm{}", self.0)?;
        Ok(())
    }
}

impl Display for FlatAtom {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            FlatAtom::Equal(lhs, rhs) => {
                write!(f, "{lhs} = {rhs}")?;
            }
            FlatAtom::Relation(rel, args) => {
                let args = args.iter().format(", ");
                write!(f, "{rel}({args})")?;
            }
            FlatAtom::Unconstrained(tm, typ) => {
                write!(f, "{tm}: {typ}")?;
            }
        }
        Ok(())
    }
}

impl Display for FlatSequent {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let premise = self
            .premise
            .iter()
            .format_with("\n", |atom, f| f(&format_args!("if {atom};")));
        let conclusion = self
            .conclusion
            .iter()
            .format_with("\n", |atom, f| f(&format_args!("then {atom};")));

        write!(f, "{premise}\n{conclusion}")
    }
}

#[cfg(debug_assertions)]
impl FlatSequent {
    pub fn check(&self) {
        let mut occurred: BTreeSet<FlatTerm> = BTreeSet::new();

        for atom in &self.premise {
            use FlatAtom::*;
            match atom {
                Equal(_, _) => panic!("FlatAtom::Equal in premise:\n{self}"),
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
                Unconstrained(_, _) => panic!("FlatAtom::Unconstrained in conclusion:\n{self}"),
                Relation(_, args) => {
                    if args.len() > 0 {
                        for arg in args[0..args.len() - 1].iter() {
                            assert!(
                                occurred.contains(arg),
                                "All but the last argument of relations must have occured earlier:\n{self}"
                            );
                        }
                    }
                    for arg in args.iter().copied() {
                        occurred.insert(arg);
                    }
                }
                Equal(lhs, rhs) => {
                    assert_ne!(lhs, rhs, "FlatAtom::Equal with equal arguments:\n{self}");
                    occurred.insert(*lhs);
                    occurred.insert(*rhs);
                }
            }
        }
    }
}
