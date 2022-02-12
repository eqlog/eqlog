use std::collections::{HashMap, HashSet};
use std::iter::once;
use std::ptr::addr_of;
use super::ast::*;
use ena::unify::{UnifyKey, EqUnifyValue, UnifyValue, NoError, InPlaceUnificationTable};

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SequentInfo {
    sequent: Box<Sequent>,
    term_indices: HashMap<*const Term, usize>,
    term_sorts: Vec<String>,
}

impl SequentInfo {
    pub fn sequent(&self) -> &Sequent {
        &self.sequent
    }
    pub fn term_index(&self, tm: &Term) -> Option<usize> {
        self.term_indices.get(&addr_of!(*tm)).map(|index| *index)
    }
    pub fn index_sort(&self, index: usize) -> Option<&str> {
        self.term_sorts.get(index).map(|s| s.as_str())
    }
    pub fn term_sort(&self, tm: &Term) -> Option<&str> {
        let index = self.term_index(tm)?;
        self.index_sort(index)
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Theory {
    sorts: HashMap<String, Sort>,
    predicates: HashMap<String, Predicate>,
    functions: HashMap<String, Function>,
    axioms: Vec<SequentInfo>,
}

impl Theory {
    pub fn new() -> Self {
        Theory {
            sorts: HashMap::new(),
            predicates: HashMap::new(),
            functions: HashMap::new(),
            axioms: Vec::new(),
        }
    }

    pub fn sorts(&self) -> &HashMap<String, Sort> { &self.sorts }
    pub fn predicates(&self) -> &HashMap<String, Predicate> { &self.predicates }
    pub fn functions(&self) -> &HashMap<String, Function> { &self.functions }
    pub fn axioms(&self) -> &[SequentInfo] { &self.axioms }

    pub fn add_sort(&mut self, sort: Sort) {
        match self.sorts.insert(sort.0.clone(), sort) {
            None => (),
            Some(prev_sort) => panic!("Duplicate declaration of sort {}", prev_sort.0)
        }
    }
    pub fn add_predicate(&mut self, pred: Predicate) {
        for s in pred.arity.iter() {
            if !self.sorts.contains_key(s) {
                panic!("Undeclared sort {}", s)
            }
        }
        match self.predicates.insert(pred.name.clone(), pred) {
            None => (),
            Some(prev_pred) => {
                panic!("Duplicate declaration of predicate {}", prev_pred.name)
            }
        }
    }
    pub fn add_function(&mut self, func: Function) {
        for s in func.dom.iter().chain(once(&func.cod)) {
            if !self.sorts.contains_key(s) {
                panic!("Undeclared sort {}", s)
            }
        }
        match self.functions.insert(func.name.clone(), func) {
            None => (),
            Some(prev_func) => {
                panic!("Duplicate declaration of function {}", prev_func.name)
            }
        }
    }
}

fn assign_wildcard_indices(mut seq: Sequent) -> Sequent {
    let mut wildcard_index = 0;
    seq.for_each_subterm_mut(|tm| {
        if let Term::Wildcard(ref mut i) = tm {
            *i = Some(wildcard_index);
            wildcard_index += 1;
        }
    });
    seq
}

fn check_epi<'a>(prem: &'a Formula, conc: &'a Formula) {
    let mut prem_vars_or_wildcards: HashSet<&'a Term> = HashSet::new();
    let is_var_or_wildcard = |tm: &Term| {
        use Term::*;
        match tm {
            Variable(_) => true,
            Wildcard(_) => true,
            Application(_, _) => false,
        }
    };
    prem.for_each_subterm(|tm| {
        if is_var_or_wildcard(tm) {
            prem_vars_or_wildcards.insert(tm);
        }
    });
    conc.for_each_subterm(|tm| {
        if is_var_or_wildcard(tm) && !prem_vars_or_wildcards.contains(tm) {
            panic!("Variable or wildcard {:?} does not appear in premise", tm);
        }
    });
}

fn make_term_indices(seq: &Sequent) -> HashMap<*const Term, usize> {
    let mut ref_map: HashMap<&Term, usize> = HashMap::new();
    let mut ptr_map: HashMap<*const Term, usize> = HashMap::new();
    seq.for_each_subterm(|tm| {
        match ref_map.get(tm) {
            Some(&i) => { let _ = ptr_map.insert(tm, i); },
            None => {
                let next_index = ref_map.len();
                let _ = ref_map.insert(tm, next_index);
                let _ = ptr_map.insert(tm, next_index);
            },
        }
    });
    ptr_map
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

fn check_surjective(prem: &Formula, conc: &Formula, indices: &HashMap<*const Term, usize>) {
    let mut table: InPlaceUnificationTable<BoolKey> = InPlaceUnificationTable::new();
    table.reserve(indices.len());
    for _ in 0 .. indices.len() {
        table.new_key(BoolOrValue(false));
    }
    prem.for_each_subterm(|tm| {
        let tm_index = *indices.get(&addr_of!(*tm)).unwrap();
        table.union_value(tm_index, BoolOrValue(true));
    });
    for atom in conc.0.iter() {
        if let Atom::Equal(lhs, rhs) = atom {
            let lhs_index = *indices.get(&addr_of!(*lhs)).unwrap();
            let rhs_index = *indices.get(&addr_of!(*rhs)).unwrap();
            table.union(lhs_index, rhs_index);
        }
    }
    conc.for_each_subterm(|tm| {
        let tm_index = *indices.get(&addr_of!(*tm)).unwrap();
        if !table.probe_value(tm_index).0 {
            panic!("Term {:?} is introduced in surjective implication", tm);
        }
    });
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct StringValue(String);
impl EqUnifyValue for StringValue {}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
struct SortKey(u32);
impl UnifyKey for SortKey {
    type Value = Option<StringValue>;
    fn index(&self) -> u32 { self.0 }
    fn from_index(i: u32) -> Self { SortKey(i) }
    fn tag() -> &'static str { "SortKey" }
}
impl From<usize> for SortKey {
    fn from(k: usize) -> SortKey { SortKey(k as u32) }
}

impl Theory {
    fn infer_sorts<'a>(
        &self,
        seq: &'a Sequent,
        indices: &HashMap<*const Term, usize>
    ) -> Vec<String> {
        let mut table: InPlaceUnificationTable<SortKey> = InPlaceUnificationTable::new();
        table.reserve(indices.len());
        for _ in 0 .. indices.len() {
            table.new_key(None);
        }

        seq.for_each_subterm(|tm| {
            use Term::*;
            let tm_index = *indices.get(&addr_of!(*tm)).unwrap();
            match tm {
                Variable(_) => (),
                Wildcard(_) => (),
                Application(func_name, args) => {
                    let function: &Function = self.functions.get(func_name).unwrap_or_else(|| {
                        panic!("Use of undeclared function {}", func_name);
                    });
                    if args.len() != function.dom.len() {
                        panic!("Wrong argument number for function {}", func_name);
                    }
                    for (arg, sort) in args.iter().zip(function.dom.iter()) {
                        let arg_index = *indices.get(&addr_of!(*arg)).unwrap();
                        table.unify_var_value(arg_index, Some(StringValue(sort.clone()))).unwrap_or_else(|_| {
                            panic!("Inferred conflicting sort for term {:?}", arg)
                        });
                    }
                    table.unify_var_value(tm_index, Some(StringValue(function.cod.clone()))).unwrap_or_else(|_| {
                        panic!("Inferred conflicting sort for term {:?}", tm)
                    });
                },
            }
        });

        let unify_term_sorts = |tbl: &mut InPlaceUnificationTable<SortKey>, lhs: &Term, rhs: &Term| {
            let lhs_index = *indices.get(&addr_of!(*lhs)).unwrap();
            let rhs_index = *indices.get(&addr_of!(*rhs)).unwrap();
            tbl.unify_var_var(lhs_index, rhs_index).unwrap_or_else(|_| {
                panic!("Inferred conflicting sorts for terms {:?} and {:?}", lhs, rhs)
            });
        };

        let process_atom = |tbl: &mut InPlaceUnificationTable<SortKey>, atom: &Atom| {
            match atom {
                Atom::Equal(lhs, rhs) => {
                    unify_term_sorts(tbl, lhs, rhs);
                },
                Atom::Defined(tm, Some(sort)) => {
                    let tm_index = *indices.get(&addr_of!(*tm)).unwrap();
                    tbl.unify_var_value(tm_index, Some(StringValue(sort.clone()))).unwrap_or_else(|_| {
                        panic!("Inferred conflicting sort for term {:?}", tm)
                    });
                },
                Atom::Defined(_, None) => (),
                Atom::Predicate(pred_name, args) => {
                    let pred: &Predicate = self.predicates.get(pred_name).unwrap_or_else(|| {
                        panic!("Use of undeclared predicate {}", pred_name);
                    });
                    if args.len() != pred.arity.len() {
                        panic!("Wrong argument number for predicate {}", pred_name);
                    }
                    for (arg, sort) in args.iter().zip(pred.arity.iter()) {
                        let arg_index = *indices.get(&addr_of!(*arg)).unwrap();
                        tbl.unify_var_value(arg_index, Some(StringValue(sort.clone()))).unwrap_or_else(|_| {
                            panic!("Inferred conflicting sort for term {:?}", arg)
                        });
                    }
                },
            }
        };

        use Sequent::*;
        match seq {
            SurjectiveImplication(prem, conc) | GeneralImplication(prem, conc) => {
                for atom in prem.0.iter().chain(conc.0.iter()) {
                    process_atom(&mut table, atom);
                }
            },
            Reduction(from, to) => {
                unify_term_sorts(&mut table, from, to);
            },
            ConditionalReduction(prem, from, to) => {
                for atom in prem.0.iter() {
                    process_atom(&mut table, atom);
                }
                unify_term_sorts(&mut table, from, to);
            },
        }

        let mut result: Vec<String> = Vec::with_capacity(indices.len());
        result.resize(indices.len(), "".to_string());
        seq.for_each_subterm(|tm| {
            let tm_index = *indices.get(&addr_of!(*tm)).unwrap();
            result[tm_index] = table.probe_value(tm_index).unwrap_or_else(|| {
                panic!("Undetermined sort for term {:?}", tm);
            }).0;
        });
        result
    }

    pub fn add_axiom(&mut self, axiom: Sequent) {
        let sequent = Box::new(assign_wildcard_indices(axiom)); 
        let term_indices = make_term_indices(&sequent);
        let term_sorts = self.infer_sorts(&sequent, &term_indices);
        use Sequent::*;
        match &*sequent {
            SurjectiveImplication(prem, conc) => check_surjective(prem, conc, &term_indices),
            GeneralImplication(prem, conc) => check_epi(prem, conc),
            Reduction(_, _) | ConditionalReduction(_, _, _) => (),
        };
        self.axioms.push(SequentInfo{sequent, term_indices, term_sorts});
    }
}
