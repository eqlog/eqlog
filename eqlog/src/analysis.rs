use crate::indirect_ast::*;
use crate::signature::Signature;
use crate::unification::{IdValMap, IdIdMap, TermUnification};
use std::convert::identity;
use std::collections::HashSet;

fn premise_terms(seq: &Sequent) -> IdValMap<Term, bool> {
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

    let mut result = IdValMap::new(seq.universe.len(), false);
    while let Some(tm) = tms.pop() {
        result[tm] = true;
        if let TermData::Application(_, args) = seq.universe.data(tm) {
            tms.extend(args);
        }
    }

    result
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct StructuralEqualityTerm(pub usize);
impl From<usize> for StructuralEqualityTerm { fn from(n: usize) -> Self { StructuralEqualityTerm(n) } }
impl Into<usize> for StructuralEqualityTerm { fn into(self) -> usize { self.0 } }
type StructuralEquality = IdIdMap<Term, StructuralEqualityTerm>;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct PremiseEqualityTerm(pub usize);
impl From<usize> for PremiseEqualityTerm { fn from(n: usize) -> Self { PremiseEqualityTerm(n) } }
impl Into<usize> for PremiseEqualityTerm { fn into(self) -> usize { self.0 } }
type PremiseEquality = IdIdMap<Term, PremiseEqualityTerm>;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct ConclusionEqualityTerm(pub usize);
impl From<usize> for ConclusionEqualityTerm { fn from(n: usize) -> Self { ConclusionEqualityTerm(n) } }
impl Into<usize> for ConclusionEqualityTerm { fn into(self) -> usize { self.0 } }
type ConclusionEquality = IdIdMap<Term, ConclusionEqualityTerm>;

fn term_equalities(sequent: &Sequent) -> (StructuralEquality, PremiseEquality, ConclusionEquality) {
    let mut unification = TermUnification::new(&sequent.universe);
    unification.congruence_closure();
    let structural_equality = unification.tabulate();

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
    let premise_equality = unification.tabulate();

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
    let conclusion_equality = unification.tabulate();

    (structural_equality, premise_equality, conclusion_equality)
}

fn infer_sorts(signature: &Signature, sequent: &Sequent, conclusion_equality: &ConclusionEquality) -> IdValMap<ConclusionEqualityTerm, String> {
    let mut sorts = IdValMap::new(conclusion_equality.range_end(), String::new());
    let mut sort_assigned: IdValMap<ConclusionEqualityTerm, bool> = IdValMap::new(conclusion_equality.range_end(), false);
    let mut assign_sort = |tm: Term, sort: &str| {
        let index = conclusion_equality[tm];
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
                let arity = match signature.predicates().get(p) {
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
                match signature.functions().get(f) {
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
        if !sort_assigned[conclusion_equality[tm]] {
            panic!("No sort inferred for term");
        }
    }

    sorts
}

fn check_epimorphism(universe: &TermUniverse, premise_terms: &IdValMap<Term, bool>) {
    let mut premise_vars: HashSet<&str> = HashSet::new();
    for (tm, data) in universe.iter_terms() {
        if premise_terms[tm] {
            match data {
                TermData::Variable(s) => { premise_vars.insert(s); },
                TermData::Wildcard | TermData::Application(_, _) => (),
            }
        }
    }
    for (tm, data) in universe.iter_terms() {
        if !premise_terms[tm] {
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
    premise_terms: &IdValMap<Term, bool>,
    conclusion_equality: &ConclusionEquality)
{
    let mut equal_to_premise_term = IdValMap::new(conclusion_equality.range_end(), false);
    for (tm, _) in universe.iter_terms() {
        if premise_terms[tm] {
            equal_to_premise_term[conclusion_equality[tm]] = true;
        }
    }
    if !equal_to_premise_term.iter().map(|(_, val)| *val).all(identity) {
        panic!("Term in conclusion surjective implication that is not equal to any term in premise")
    }
}

pub struct SequentAnalysis {
    pub premise_terms: IdValMap<Term, bool>,
    pub structural_equality: StructuralEquality,
    pub premise_equality: PremiseEquality,
    pub conclusion_equality: ConclusionEquality,
    pub sorts: IdValMap<ConclusionEqualityTerm, String>,
}

pub fn analyze(signature: &Signature, sequent: &Sequent) -> SequentAnalysis {
    let premise_terms = premise_terms(sequent);
    let (structural_equality, premise_equality, conclusion_equality) = term_equalities(sequent);
    let sorts = infer_sorts(signature, sequent, &conclusion_equality);
    check_epimorphism(&sequent.universe, &premise_terms);
    use SequentData::*;
    match &sequent.data {
        SurjectiveImplication(_, _) => {
            check_surjective(&sequent.universe, &premise_terms, &conclusion_equality);
        },
        GeneralImplication(_, _) | Reduction(_, _) | ConditionalReduction(_, _, _) => (),
    }
    SequentAnalysis {
        premise_terms,
        structural_equality,
        premise_equality,
        conclusion_equality,
        sorts,
    }
}

#[cfg(test)]
mod tests {

use indoc::indoc;

use crate::grammar::TheoryParser;
use crate::indirect_ast::*;
use crate::unification::IdValMap;

#[test]
fn good_theory() {
    let src = indoc! {"
        Sort obj;
        Sort mor;

        Func comp : mor * mor -> mor;
        Axiom comp(h, comp(g, f)) ~> comp(comp(h, g), f);

        Pred signature: obj * mor * obj;

        Axiom signature(x, f, y) & signature(y, g, z) =!> signature(x, comp(g, f), z);

        Func id : obj -> mor; Axiom g = comp(f, id(_)) => f = g;
    "};
    let (sig, axioms) = TheoryParser::new().parse(src).unwrap();
    let obj = || { "obj".to_string() };
    let mor = || { "mor".to_string() };
    let comp = || { "comp".to_string() };
    let id = || { "id".to_string() };
    let signature = || { "signature".to_string() };

    assert_eq!(
        *sig.sorts(),
        hashmap!{
            obj() => Sort(obj()),
            mor() => Sort(mor()),
        }
    );
    assert_eq!(
        *sig.functions(),
        hashmap!{
            comp() => Function{name: comp(), dom: vec![mor(), mor()], cod: mor()},
            id() => Function{name: id(), dom: vec![obj()], cod: mor()},
        }
    );
    assert_eq!(
        *sig.predicates(),
        hashmap!{
            signature() => Predicate{name: signature(), arity: vec![obj(), mor(), obj()]},
        }
    );

    use TermData::*;
    let f = || { Variable("f".to_string()) };
    let g = || { Variable("g".to_string()) };
    let h = || { Variable("h".to_string()) };
    let x = || { Variable("x".to_string()) };
    let y = || { Variable("y".to_string()) };
    let z = || { Variable("z".to_string()) };

    let ((seq0, ana0), (seq1, ana1), (seq2, ana2)) = match axioms.as_slice() {
        [ax0, ax1, ax2] => (ax0, ax1, ax2),
        _ => panic!("{}", axioms.len()),
    };

    {
        let mut universe = TermUniverse::new();
        let mut premise_terms: Vec<bool> = Vec::new();
        let mut structural_equality: Vec<usize> = Vec::new();

        let h0 = universe.new_term(h());
        premise_terms.push(true);
        structural_equality.push(0);
        let g0 = universe.new_term(g());
        premise_terms.push(true);
        structural_equality.push(1);
        let f0 = universe.new_term(f());
        premise_terms.push(true);
        structural_equality.push(2);
        let gf = universe.new_term(Application(comp(), vec![g0, f0]));
        premise_terms.push(true);
        structural_equality.push(3);
        let h_gf = universe.new_term(Application(comp(), vec![h0, gf]));
        premise_terms.push(false);
        structural_equality.push(4);

        let h1 = universe.new_term(h());
        premise_terms.push(true);
        structural_equality.push(0);
        let g1 = universe.new_term(g());
        premise_terms.push(true);
        structural_equality.push(1);
        let hg = universe.new_term(Application(comp(), vec![h1, g1]));
        premise_terms.push(true);
        structural_equality.push(5);
        let f1 = universe.new_term(f());
        premise_terms.push(true);
        structural_equality.push(2);
        let hg_f = universe.new_term(Application(comp(), vec![hg, f1]));
        premise_terms.push(true);
        structural_equality.push(6);

        let data = SequentData::Reduction(h_gf, hg_f);

        assert_eq!(seq0.data, data);
        assert_eq!(seq0.universe, universe);

        assert_eq!(ana0.premise_terms, IdValMap::from_table(premise_terms));

        assert_eq!(ana0.structural_equality[f0], ana0.structural_equality[f1]);
        assert_eq!(ana0.structural_equality[g0], ana0.structural_equality[g1]);
        assert_eq!(ana0.structural_equality[h0], ana0.structural_equality[h1]);

        // TODO: Check that they are *permutations* of on another.
        //assert_eq!(ana0.premise_equality, ana0.structural_equality);
        assert_eq!(ana0.conclusion_equality[h_gf], ana0.conclusion_equality[hg_f]);

        assert_eq!(ana0.sorts[ana0.conclusion_equality[f0]], mor());
        assert_eq!(ana0.sorts[ana0.conclusion_equality[g0]], mor());
        assert_eq!(ana0.sorts[ana0.conclusion_equality[h0]], mor());
        assert_eq!(ana0.sorts[ana0.conclusion_equality[hg]], mor());
        assert_eq!(ana0.sorts[ana0.conclusion_equality[gf]], mor());
        assert_eq!(ana0.sorts[ana0.conclusion_equality[h_gf]], mor());
        assert_eq!(ana0.sorts[ana0.conclusion_equality[hg_f]], mor());
    }

    {
        let mut universe = TermUniverse::new();
        let mut premise_terms: Vec<bool> = Vec::new();

        let x0 = universe.new_term(x());
        premise_terms.push(true);
        let f0 = universe.new_term(f());
        premise_terms.push(true);
        let y0 = universe.new_term(y());
        premise_terms.push(true);
        let sig_f = Atom::Predicate(signature(), vec![x0, f0, y0]);

        let y1 = universe.new_term(y());
        premise_terms.push(true);
        let g0 = universe.new_term(g());
        premise_terms.push(true);
        let z0 = universe.new_term(z());
        premise_terms.push(true);
        let sig_g = Atom::Predicate(signature(), vec![y1, g0, z0]);

        let x1 = universe.new_term(x());
        premise_terms.push(false);
        let g1 = universe.new_term(g());
        premise_terms.push(false);
        let f1 = universe.new_term(f());
        premise_terms.push(false);
        let gf = universe.new_term(Application(comp(), vec![g1, f1]));
        premise_terms.push(false);
        let z1 = universe.new_term(z());
        premise_terms.push(false);
        let sig_gf = Atom::Predicate(signature(), vec![x1, gf, z1]);

        let data = SequentData::GeneralImplication(
            Formula(vec![sig_f, sig_g]),
            Formula(vec![sig_gf])
        );
        assert_eq!(seq1.data, data);
        assert_eq!(seq1.universe, universe);

        assert_eq!(ana1.premise_terms, IdValMap::from_table(premise_terms));

        assert_eq!(ana1.structural_equality[f0], ana1.structural_equality[f1]);
        assert_eq!(ana1.structural_equality[g0], ana1.structural_equality[g1]);
        assert_eq!(ana1.structural_equality[x0], ana1.structural_equality[x1]);
        assert_eq!(ana1.structural_equality[y0], ana1.structural_equality[y1]);
        assert_eq!(ana1.structural_equality[z0], ana1.structural_equality[z1]);

        // TODO: Check that they are *permutations* of on another.
        //assert_eq!(ana1.structural_equality, ana1.premise_equality);
        //assert_eq!(ana1.structural_equality, ana1.conclusion_equality);

        assert_eq!(ana1.sorts[ana1.conclusion_equality[x0]], obj());
        assert_eq!(ana1.sorts[ana1.conclusion_equality[y0]], obj());
        assert_eq!(ana1.sorts[ana1.conclusion_equality[z0]], obj());
        assert_eq!(ana1.sorts[ana1.conclusion_equality[f0]], mor());
        assert_eq!(ana1.sorts[ana1.conclusion_equality[g0]], mor());
        assert_eq!(ana1.sorts[ana1.conclusion_equality[gf]], mor());
    }

    {
        let mut universe = TermUniverse::new();
        let mut premise_terms: Vec<bool> = Vec::new();

        let g0 = universe.new_term(g());
        premise_terms.push(true);
        let f0 = universe.new_term(f());
        premise_terms.push(true);
        let wc = universe.new_term(Wildcard);
        premise_terms.push(true);
        let i = universe.new_term(Application(id(), vec![wc]));
        premise_terms.push(true);
        let fi = universe.new_term(Application(comp(), vec![f0, i]));
        premise_terms.push(true);
        let prem_eq = Atom::Equal(g0, fi);

        let f1 = universe.new_term(f());
        premise_terms.push(false);
        let g1 = universe.new_term(g());
        premise_terms.push(false);
        let conc_eq = Atom::Equal(f1, g1);

        let data = SequentData::SurjectiveImplication(
            Formula(vec![prem_eq]),
            Formula(vec![conc_eq])
        );

        assert_eq!(seq2.data, data);
        assert_eq!(seq2.universe, universe);

        assert_eq!(ana2.premise_terms, IdValMap::from_table(premise_terms));

        assert_eq!(ana2.structural_equality[f0], ana2.structural_equality[f1]);
        assert_eq!(ana2.structural_equality[g0], ana2.structural_equality[g1]);
        assert_eq!(ana2.premise_equality[g0], ana2.premise_equality[fi]);
        assert_ne!(ana2.premise_equality[f1], ana2.premise_equality[g1]);
        assert_eq!(ana2.conclusion_equality[f1], ana2.conclusion_equality[g1]);

        assert_eq!(ana2.sorts[ana2.conclusion_equality[f0]], mor());
        assert_eq!(ana2.sorts[ana2.conclusion_equality[g0]], mor());
        assert_eq!(ana2.sorts[ana2.conclusion_equality[i]], mor());
        assert_eq!(ana2.sorts[ana2.conclusion_equality[fi]], mor());
    }
}

#[test] #[should_panic]
fn wrong_function_argument_number() {
    let src = indoc! {"
        Sort mor;
        Func comp : mor * mor -> mor;
        Axiom comp(g, f, h) ~> g;
    "};
    TheoryParser::new().parse(src).unwrap();
}

#[test] #[should_panic]
fn conflicting_sorts_equality() {
    let src = indoc! {"
        Sort obj;
        Sort mor;
        Func id : obj -> mor;
        Axiom id(x) = f => x = f;
    "};
    TheoryParser::new().parse(src).unwrap();
}

#[test] #[should_panic]
fn conflicting_sorts_reduction() {
    let src = indoc! {"
        Sort obj;
        Sort mor;
        Func id : obj -> mor;
        Axiom id(x) ~> x;
    "};
    TheoryParser::new().parse(src).unwrap();
}

#[test] #[should_panic]
fn conflicting_sorts_predicate() {
    let src = indoc! {"
        Sort obj;
        Sort mor;
        Pred is_id : mor * obj;
        Axiom is_id(f, x) => is_id(x, f);
    "};
    TheoryParser::new().parse(src).unwrap();
}

#[test] #[should_panic]
fn non_epi() {
    let src = indoc! {"
        Sort obj;
        Sort mor;
        Func id : obj -> mor;
        Axiom id(x) = f =!> f = g;
    "};
    TheoryParser::new().parse(src).unwrap();
}

#[test] #[should_panic]
fn non_surjective0() {
    let src = indoc! {"
        Sort obj;
        Sort mor;
        Pred signature: obj * mor * obj;
        Func id : obj -> mor;
        Func comp : mor * mor -> mor;
        Axiom signature(x, f, _) => comp(f, id(x)) = f;
    "};
    TheoryParser::new().parse(src).unwrap();
}

#[test] #[should_panic]
fn non_surjective1() {
    let src = indoc! {"
        Sort obj;
        Sort mor;
        Func id : obj -> mor;
        Axiom x = y => id(x) = id(y);
    "};
    TheoryParser::new().parse(src).unwrap();
}

#[test] #[should_panic]
fn no_sort_inferred() {
    let src = indoc! {"
        Sort obj;
        Axiom x = y => y = x;
    "};
    TheoryParser::new().parse(src).unwrap();
}

}
