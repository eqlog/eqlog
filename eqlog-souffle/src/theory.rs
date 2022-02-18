use std::collections::{HashSet,HashMap};
use crate::indirect_ast::*;
use std::iter::once;
use crate::unification::TermUnification;
use std::convert::identity;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AnalyzedSequent {
    pub sequent: Sequent,
    pub premise_terms: Vec<bool>,
    pub structural_equality: Vec<usize>,
    pub premise_equality: Vec<usize>,
    pub conclusion_equality: Vec<usize>,
    pub sorts: Vec<String>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Theory {
    sorts: HashMap<String, Sort>,
    predicates: HashMap<String, Predicate>,
    functions: HashMap<String, Function>,
    axioms: Vec<AnalyzedSequent>,
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
    pub fn axioms(&self) -> &[AnalyzedSequent] { &self.axioms }

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

fn premise_terms(seq: &Sequent) -> Vec<bool> {
    let mut tms: Vec<Term> = Vec::new();
    use SequentData::*;
    match &seq.data {
        SurjectiveImplication(prem, _) | GeneralImplication(prem, _) | ConditionalReduction(prem, _, _) => {
            for atom in prem.0.iter() {
                match atom {
                    Atom::Equal(lhs, rhs) => tms.extend([*lhs, *rhs].iter()),
                    Atom::Defined(tm, _) => tms.push(*tm),
                    Atom::Predicate(_, args) => tms.extend(args),
                }
            }
        },
        Reduction(_, _) => (),
    }
    match &seq.data {
        Reduction(from, to) | ConditionalReduction(_, from, to) => {
            tms.push(*to);
            if let TermData::Application(_, args) = seq.universe.data(*from) {
                tms.extend(args);
            }
        },
        SurjectiveImplication(_, _) | GeneralImplication(_, _) => (),
    }

    let mut result: Vec<bool> = (0 .. seq.universe.len()).map(|_| false).collect();
    while let Some(tm) = tms.pop() {
        result[tm.0] = true;
        if let TermData::Application(_, args) = seq.universe.data(tm) {
            tms.extend(args);
        }
    }

    result
}

fn term_equalities(sequent: &Sequent) -> (Vec<usize>, Vec<usize>, Vec<usize>) {
    let mut unification = TermUnification::new(&sequent.universe);
    unification.congruence_closure();
    let structural_equality = unification.tabulate().1;

    use SequentData::*;
    match &sequent.data {
        SurjectiveImplication(prem, _) | GeneralImplication(prem, _) | ConditionalReduction(prem, _, _) => {
            for atom in prem.0.iter() {
                use Atom::*;
                match atom {
                    Equal(lhs, rhs) => unification.union(*lhs, *rhs),
                    Predicate(_, _) => (),
                    Defined(_, _) => (),
                }
            }
        },
        Reduction(_, _) => (),
    }
    unification.congruence_closure();
    let premise_equality = unification.tabulate().1;

    match &sequent.data {
        SurjectiveImplication(_, conc) | GeneralImplication(_, conc) => {
            for atom in conc.0.iter() {
                use Atom::*;
                match atom {
                    Equal(lhs, rhs) => unification.union(*lhs, *rhs),
                    Predicate(_, _) => (),
                    Defined(_, _) => (),
                }
            }
        },
        Reduction(from, to) | ConditionalReduction(_, from, to) => {
            unification.union(*from, *to);
        },
    }
    unification.congruence_closure();
    let conclusion_equality = unification.tabulate().1;

    (structural_equality, premise_equality, conclusion_equality)
}

impl Theory {
    pub fn analyze_sequent(&mut self, sequent: Sequent) -> AnalyzedSequent {
        let premise_terms = premise_terms(&sequent);
        let (structural_equality, premise_equality, conclusion_equality) =
            term_equalities(&sequent);

        let conc_eq_max = conclusion_equality.iter().copied().max().unwrap();
        let mut sorts: Vec<String> = (0 .. conc_eq_max + 1).map(|_| String::new()).collect();
        let mut sort_assigned: Vec<bool> = (0 .. sorts.len()).map(|_| false).collect();
        let mut assign_sort = |tm: Term, sort: &str| {
            let index = conclusion_equality[tm.0];
            if sort_assigned[index] && sorts[index] != sort {
                panic!("Conflicting sorts inferred for term: {} and {}", sort, sorts[index]);
            } else {
                sort_assigned[index] = true;
                sorts[index] = sort.to_string();
            }
        };

        use SequentData::*;
        let (prem_atoms, conc_atoms): (&[Atom], &[Atom]) = match &sequent.data {
            SurjectiveImplication(prem, conc) | GeneralImplication(prem, conc) => {
                (prem.0.as_slice(), conc.0.as_slice())
            },
            ConditionalReduction(prem, _, _) => {
                (prem.0.as_slice(), &[])
            },
            Reduction(_, _) => {
                (&[], &[])
            },
        };

        for atom in prem_atoms.iter().chain(conc_atoms) {
            match atom {
                Atom::Equal(_, _) => (),
                Atom::Defined(tm, Some(sort)) => assign_sort(*tm, sort),
                Atom::Defined(_, None) => (),
                Atom::Predicate(p, args) => {
                    let arity = match self.predicates.get(p) {
                        Some(Predicate{arity, ..}) => arity,
                        None => panic!("Undeclared predicate {}", p),
                    };
                    if args.len() != arity.len() {
                        panic!("Wrong argument number for predicate {}", p)
                    }
                    for (arg, sort) in args.iter().copied().zip(arity) {
                        assign_sort(arg, sort);
                    }
                },
            }
        }

        for (tm, data) in sequent.universe.iter_terms() {
            match data {
                TermData::Application(f, args) => {
                    match self.functions.get(f) {
                        Some(Function{dom, cod, ..}) => {
                            if args.len() != dom.len() {
                                panic!("Wrong argument number for function {}", f)
                            }
                            for (arg, sort) in args.iter().copied().zip(dom) {
                                assign_sort(arg, sort);
                            }
                            assign_sort(tm, cod);
                        },
                        None => panic!("Undeclared function {}", f),
                    }
                },
                TermData::Wildcard | TermData::Variable(_) => (),
            }
        }

        for (tm, _) in sequent.universe.iter_terms() {
            if !sort_assigned[conclusion_equality[tm.0]] {
                panic!("No sort inferred for term");
            }
        }

        AnalyzedSequent{
            sequent,
            premise_terms,
            structural_equality,
            premise_equality,
            conclusion_equality,
            sorts,
        }
    }
}

fn check_epimorphism(universe: &TermUniverse, premise_terms: &[bool]) {
    let mut premise_vars: HashSet<&str> = HashSet::new();
    for (tm, data) in universe.iter_terms() {
        if premise_terms[tm.0] {
            match data {
                TermData::Variable(s) => { premise_vars.insert(s); },
                TermData::Wildcard | TermData::Application(_, _) => (),
            }
        }
    }
    for (tm, data) in universe.iter_terms() {
        if !premise_terms[tm.0] {
            match data {
                TermData::Variable(s) => {
                    if !premise_vars.contains(s.as_str()) {
                        panic!("Variable {} in conclusion does not appear in premise", s)
                    }
                },
                TermData::Wildcard => panic!("Wildcard in conclusion"),
                TermData::Application(_, _) => (),
            }
        }
    }
}
fn check_surjective(
    universe: &TermUniverse,
    premise_terms: &[bool],
    conclusion_equality: &[usize])
{
    let conc_eq_max = conclusion_equality.iter().copied().max().unwrap();
    let mut equal_to_premise_term: Vec<bool> = Vec::new();
    equal_to_premise_term.resize(conc_eq_max + 1, false);
    for (tm, _) in universe.iter_terms() {
        if premise_terms[tm.0] {
            equal_to_premise_term[conclusion_equality[tm.0]] = true;
        }
    }
    if !equal_to_premise_term.iter().copied().all(identity) {
        panic!("Term in conclusion surjective implication that is not equal to any term in premise")
    }
}

impl Theory {
    pub fn add_axiom(&mut self, sequent: Sequent) {
        let analyzed = self.analyze_sequent(sequent);
        use SequentData::*;
        check_epimorphism(&analyzed.sequent.universe, &analyzed.premise_terms);
        match &analyzed.sequent.data {
            SurjectiveImplication(_, _) => {
                check_surjective(&analyzed.sequent.universe, &analyzed.premise_terms, &analyzed.conclusion_equality);
            },
            GeneralImplication(_, _) | Reduction(_, _) | ConditionalReduction(_, _, _) => (),
        }
        self.axioms.push(analyzed);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sorts_predicates_functions() {
        let mut th = Theory::new();
        let s = || "S".to_string();
        let t = || "T".to_string();
        th.add_sort(Sort(s()));
        th.add_sort(Sort(t()));

        th.add_predicate(Predicate{name: "Q".to_string(), arity: vec![s(), t()]});
        th.add_predicate(Predicate{name: "P".to_string(), arity: vec![s(), s(), s()]});

        th.add_function(Function{name: "F".to_string(), dom: vec![s(), t()], cod: t()});
        th.add_function(Function{name: "G".to_string(), dom: vec![t(), s()], cod: t()});
    }

    #[test] #[should_panic]
    fn test_duplicate_sort() {
        let mut th = Theory::new();
        let s = || "S".to_string();
        let t = || "T".to_string();
        th.add_sort(Sort(s()));
        th.add_sort(Sort(t()));
        th.add_sort(Sort(s()));
    }

    #[test] #[should_panic]
    fn test_duplicate_predicate() {
        let mut th = Theory::new();
        let s = || "S".to_string();
        let t = || "T".to_string();
        th.add_sort(Sort(s()));
        th.add_sort(Sort(t()));

        th.add_predicate(Predicate{name: "Q".to_string(), arity: vec![s(), t()]});
        th.add_predicate(Predicate{name: "P".to_string(), arity: vec![s(), s(), s()]});
        th.add_predicate(Predicate{name: "Q".to_string(), arity: vec![t(), s()]});
    }

    #[test] #[should_panic]
    fn test_duplicate_function() {
        let mut th = Theory::new();
        let s = || "S".to_string();
        let t = || "T".to_string();
        th.add_sort(Sort(s()));
        th.add_sort(Sort(t()));

        th.add_function(Function{name: "F".to_string(), dom: vec![s(), t()], cod: t()});
        th.add_function(Function{name: "G".to_string(), dom: vec![t(), s()], cod: t()});
        th.add_function(Function{name: "F".to_string(), dom: vec![s(), t()], cod: t()});
    }

    #[test] #[should_panic]
    fn test_predicate_bad_arity() {
        let mut th = Theory::new();
        let s = || "S".to_string();
        let t = || "T".to_string();
        th.add_sort(Sort(s()));

        th.add_predicate(Predicate{name: "Q".to_string(), arity: vec![s(), t()]});
    }

    #[test] #[should_panic]
    fn test_function_bad_dom() {
        let mut th = Theory::new();
        let s = || "S".to_string();
        let t = || "T".to_string();
        th.add_sort(Sort(s()));

        th.add_function(Function{name: "F".to_string(), dom: vec![s(), s()], cod: t()});
    }

    #[test] #[should_panic]
    fn test_function_bad_cod() {
        let mut th = Theory::new();
        let s = || "S".to_string();
        let t = || "T".to_string();
        th.add_sort(Sort(s()));

        th.add_function(Function{name: "F".to_string(), dom: vec![s(), t(), s()], cod: s()});
    }
}
