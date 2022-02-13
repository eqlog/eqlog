use crate::theory::*;
use crate::ast::{self, Ast};
use crate::ram;
use std::iter::once;
use ena::unify::{UnifyKey, UnifyValue, NoError, InPlaceUnificationTable};
use std::ptr::addr_of;
use std::collections::HashMap;

pub fn theory_to_machine(th: &Theory) -> ram::Machine {
    let predicate_relations = 
        th.predicates().iter()
        .map(|(_, p)| (p.name.clone(), p.arity.clone()));
    // TODO: Rule out that function and predicate has the same name.
    let function_relations = 
        th.functions().iter()
        .map(|(_, f)| {
            let name = f.name.clone();
            let arity = f.dom.iter().cloned().chain(once(f.cod.clone())).collect();
            (name, arity)
        });       
    ram::Machine {
        sorts: th.sorts().iter().map(|(s, _)| s.clone()).collect(),
        relations:
            predicate_relations
            .chain(function_relations)
            .collect(),
    }
}

struct ExtendedSequentInfo<'a> {
    sequent_info: &'a SequentInfo,
    is_first_alpha_occurence: HashMap<*const ast::Term, bool>,
    premise_equality_names: Vec<String>,
    is_free_variable_in_premise: Vec<bool>,
    is_in_premise: Vec<bool>,
}

fn compute_first_alpha_occurences(si: &SequentInfo) -> HashMap<*const ast::Term, bool> {
    let mut has_occured: Vec<bool> = (0 .. si.index_len()).map(|_| false).collect();
    let mut result: HashMap<*const ast::Term, bool> = HashMap::new();
    si.sequent().for_each_subterm(|tm| {
        let index = si.term_index(tm).unwrap(); 
        result.insert(addr_of!(*tm), !has_occured[index]);
        has_occured[index] = true;
    });
    result
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct VariableValue(String);
impl UnifyValue for VariableValue {
    type Error = NoError;
    fn unify_values(lhs: &VariableValue, rhs: &VariableValue) -> Result<Self, NoError> {
        Ok(VariableValue(format!("{}__{}", lhs.0, rhs.0)))
    }
}
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
struct StringKey(u32);
impl UnifyKey for StringKey {
    type Value = VariableValue;
    fn index(&self) -> u32 { self.0 }
    fn from_index(i: u32) -> Self { StringKey(i) }
    fn tag() -> &'static str { "StringKey" }
}
impl From<usize> for StringKey {
    fn from(k: usize) -> Self { StringKey(k as u32) }
}

fn premise_equality_names(si: &SequentInfo) -> Vec<String> {
    let index_terms: Vec<(usize, &ast::Term)> = {
        let mut index_terms: Vec<(usize, &ast::Term)> = Vec::new();
        si.sequent().for_each_subterm(|tm| {
            index_terms.push((si.term_index(tm).unwrap(), tm));
        });
        index_terms.sort_by_key(|(index, _)| *index);
        index_terms.dedup_by_key(|(index, _)| *index);
        index_terms
    };

    let mut table: InPlaceUnificationTable<StringKey> = InPlaceUnificationTable::new();
    for &(index, tm) in index_terms.iter() {
        let base_name = match tm {
            ast::Term::Variable(s) => s,
            ast::Term::Wildcard(_) => "_",
            ast::Term::Application(f, _) => f,
        };
        let key = table.new_key(VariableValue(format!("{}{}", base_name, index)));
        debug_assert_eq!(key, StringKey::from(index));
    }

    use ast::Sequent::*;
    match si.sequent() {
        ast::Sequent::Reduction(_, _) => (),
        SurjectiveImplication(prem, _) | GeneralImplication(prem, _) | ConditionalReduction(prem, _, _) => {
            for atom in prem.0.iter() {
                match atom {
                    ast::Atom::Equal(lhs, rhs) => {
                        table.union(si.term_index(lhs).unwrap(), si.term_index(rhs).unwrap());
                    },
                    _ => {},
                }
            }
        },
    };

    let mut result: Vec<String> = Vec::with_capacity(index_terms.len());
    for i in 0 .. index_terms.len() {
        result.push(table.probe_value(i).0);
    }
    result
}

fn free_premise_terms(si: &SequentInfo) -> Vec<bool> {
    let mut is_free: Vec<bool> = (0 .. si.index_len()).map(|_| true).collect();
    let mut mark_bound = |tm: &ast::Term| {
        is_free[si.term_index(tm).unwrap()] = false;
    };

    use ast::Sequent::*;
    match si.sequent() {
        Reduction(_, _) => (),
        SurjectiveImplication(prem, _) | GeneralImplication(prem, _) | ConditionalReduction(prem, _, _) => {
            for atom in prem.0.iter() {
                match atom {
                    ast::Atom::Predicate(_, args) => args.iter().for_each(&mut mark_bound),
                    ast::Atom::Equal(_, _) | ast::Atom:: Defined(_, _) => (),
                }
            }
            prem.for_each_subterm(|tm| {
                match tm {
                    ast::Term::Application(_, args) => {
                        mark_bound(tm);
                        args.iter().for_each(&mut mark_bound);
                    },
                    ast::Term::Variable(_) | ast::Term::Wildcard(_) => (),
                }
            });
        },
    }

    match si.sequent() {
        SurjectiveImplication(_, _) | GeneralImplication(_, _) => (),
        Reduction(from, to) | ConditionalReduction(_, from, to) => {
            to.for_each_subterm(|tm| {
                match tm {
                    ast::Term::Application(_, args) => {
                        mark_bound(tm);
                        args.iter().for_each(&mut mark_bound);
                    },
                    ast::Term::Variable(_) | ast::Term::Wildcard(_) => (),
                }
            });
            from.for_each_subterm(|tm| {
                if addr_of!(*tm) != addr_of!(*from) {
                    match tm {
                        ast::Term::Application(_, args) => {
                            mark_bound(tm);
                            args.iter().for_each(&mut mark_bound);
                        },
                        ast::Term::Variable(_) | ast::Term::Wildcard(_) => (),
                    }
                }
            });
        },
    }

    is_free
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct BoolOrValue(bool);
impl UnifyValue for BoolOrValue {
    type Error = NoError;
    fn unify_values(lhs: &BoolOrValue, rhs: &BoolOrValue) -> Result<Self, NoError> {
        Ok(BoolOrValue(lhs.0 || rhs.0))
    }
}
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
struct BoolKey(u32);
impl UnifyKey for BoolKey {
    type Value = BoolOrValue;
    fn index(&self) -> u32 { self.0 }
    fn from_index(i: u32) -> Self { BoolKey(i) }
    fn tag() -> &'static str { "BoolKey" }
}
impl From<usize> for BoolKey {
    fn from(k: usize) -> Self { BoolKey(k as u32) }
}

fn premise_terms(si: &SequentInfo) -> Vec<bool> {
    use ast::Sequent::*;
    let (prem, conc) = match si.sequent() {
        Reduction(_, _) | SurjectiveImplication(_, _) | ConditionalReduction(_, _, _) => {
            return (0 .. si.index_len()).map(|_| true).collect();
        },
        GeneralImplication(prem, conc) => (prem, conc),
    };

    let mut table: InPlaceUnificationTable<BoolKey> = InPlaceUnificationTable::new();
    table.reserve(si.index_len());
    for _ in 0 .. si.index_len() {
        table.new_key(BoolOrValue(false));
    }
    
    prem.for_each_subterm(|tm| {
        let index = si.term_index(tm).unwrap();
        table.union_value(index, BoolOrValue(true));
    });

    for atom in conc.0.iter() {
        if let ast::Atom::Equal(lhs, rhs) = atom {
            let lhs_index = si.term_index(lhs).unwrap();
            let rhs_index = si.term_index(rhs).unwrap();
            table.union(lhs_index, rhs_index);
        }
    }

    return (0 .. si.index_len()).map(|index| table.probe_value(index).0).collect()
}

impl<'a> ExtendedSequentInfo<'a> {
    fn new(si: &'a SequentInfo) -> ExtendedSequentInfo<'a> {
        ExtendedSequentInfo {
            sequent_info: si,
            is_first_alpha_occurence: compute_first_alpha_occurences(si),
            premise_equality_names: premise_equality_names(si),
            is_free_variable_in_premise: free_premise_terms(si),
            is_in_premise: premise_terms(si),
        }
    }
}

// enum FlatAtom {
//     Relation{name:String, args: Vec<String>},
//     Element{name:String, sort: String},
//     Equality(String, String),
// }
// 
// struct FlatSequent {
//     premise: Vec<FlatAtom>,
//     conclusion: Vec<FlatAtom>,
// }
// 
// fn flatten_sequent(si: &SequentInfo) -> FlatSequent {
//     let names = term_names(si);
//     let mut premise: Vec<FlatAtom> = Vec::new();
//     let mut is_free_in_premise: Vec<bool> = free_premise_terms(si);
// 
//     let mut term_added: Vec<bool> = (0 .. names.len()).map(|_| false).collect();
//     let mut mark_term_added = |tm: &ast::Term| -> bool {
//         let index = si.term_index(tm).unwrap();
//         let val = term_added[index];
//         term_added[index] = true;
//         val
//     };
// 
//     let term_atom = |tm: &ast::Term| -> Option<FlatAtom> {
//         let index = si.term_index(tm).unwrap();
//         match tm {
//             ast::Term::Application(f, args) => {
//                 let rel_args =
//                     args.iter()
//                     .map(|arg| names[si.term_index(arg).unwrap()].clone())
//                     .chain(once(names[index].clone()))
//                     .collect();
//                 Some(FlatAtom::Relation {
//                     name: f.clone(),
//                     args: rel_args,
//                 })
//             },
//             ast::Term::Wildcard(_) | ast::Term::Variable(_) => None,
//         }
//     };
// 
//     use ast::Sequent::*;
//     let premise_atoms: &[ast::Atom] = match si.sequent() {
//         Reduction(_, _) => &[],
//         SurjectiveImplication(prem, _) | GeneralImplication(prem, _) | ConditionalReduction(prem, _, _) => {
//             prem.0.as_slice()
//         },
//     };
//     for atom in premise_atoms {
//         match atom {
//             ast::Atom::Equal(lhs, rhs) => {
//                 for tm in &[lhs, rhs] {
//                     tm.for_each_subterm(|tm| {
//                         if !mark_term_added(tm) {
//                             premise.extend(term_atom(tm));
//                         }
//                     });
//                 }
//                 debug_assert_eq!(names[si.term_index(lhs).unwrap()], names[si.term_index(rhs).unwrap()]);
//             },
//             ast::Atom::Defined(tm, _) => {
//                 tm.for_each_subterm(|tm| {
//                     if !mark_term_added(tm) {
//                         premise.extend(term_atom(tm));
//                     }
//                 });
//                 let index = si.term_index(tm).unwrap();
//                 if is_free_in_premise[index] {
//                     premise.push(FlatAtom::Element{
//                         name: names[index].clone(),
//                         sort: si.index_sort(index).unwrap().to_string(),
//                     });
//                 }
//             },
//             ast::Atom::Predicate(p, args) => {
//                 let mut rel_args = Vec::with_capacity(args.len());
//                 for arg in args {
//                     arg.for_each_subterm(|tm| {
//                         if !mark_term_added(tm) {
//                             premise.extend(term_atom(arg));
//                         }
//                     });
//                     let index = si.term_index(arg).unwrap();
//                     rel_args.push(names[index].clone());
//                 }
//                 premise.push(FlatAtom::Relation {
//                     name: p.clone(),
//                     args: rel_args,
//                 });
//             },
//         }
//     }
// 
//     match si.sequent() {
//         SurjectiveImplication(_, _) | GeneralImplication(_, _) => (),
//         Reduction(from, to) | ConditionalReduction(_, from, to) => {
//             to.for_each_subterm(|tm| {
//                 if !mark_term_added(tm) {
//                     premise.extend(term_atom(tm));
//                 }
//             });
//             from.for_each_subterm(|tm| {
//                 if !mark_term_added(tm) && addr_of!(*tm) != addr_of!(*from) {
//                     premise.extend(term_atom(tm));
//                 }
//             });
//         },
//     }
// 
//     let conclusion_atoms: &[ast::Atom] = match si.sequent() {
//         Reduction(_, _) | ConditionalReduction(_, _, _) => &[],
//         SurjectiveImplication(_, conc) | GeneralImplication(_, conc) => {
//             conc.0.as_slice()
//         },
//     };
// 
//     panic!()
// }
