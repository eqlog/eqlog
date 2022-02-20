use crate::indirect_ast::*;
use crate::analysis::*;
use crate::unification::IdValMap;
use std::iter::once;

pub type FlatTerm = PremiseEqualityTerm;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum FlatAtom {
    Equal(FlatTerm, FlatTerm),
    Relation(String, Vec<FlatTerm>),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FlatSequent {
    pub premise: Vec<FlatAtom>,
    pub conclusion: Vec<FlatAtom>,
}

fn flatten_term(
    universe: &TermUniverse,
    premise_equality: &PremiseEquality,
    first_structural_occurence: &IdValMap<Term, bool>,
    term: Term,
) -> Option<FlatAtom> {
    if !first_structural_occurence[term] {
        return None;
    }

    use TermData::*;
    match universe.data(term) {
        Variable(_) | Wildcard => None,
        Application(func_name, args) => {
            let rel_args: Vec<FlatTerm> =
                args.iter().copied()
                .chain(once(term))
                .map(|arg| premise_equality[arg])
                .collect();
            Some(FlatAtom::Relation(func_name.clone(), rel_args))
        },
    }
}

fn flatten_atom(
    universe: &TermUniverse,
    premise_equality: &PremiseEquality,
    first_structural_occurence: &IdValMap<Term, bool>,
    atom: &Atom,
) -> Vec<FlatAtom> {
    let mut flat_atoms = vec![];
    for tm in (atom.terms_begin.0 .. atom.terms_end.0).map(Term) {
        flat_atoms.extend(flatten_term(universe, premise_equality, first_structural_occurence, tm));
    }

    use AtomData::*;
    match &atom.data {
        Equal(lhs, rhs) => {
            let lhs_prem = premise_equality[*lhs];
            let rhs_prem = premise_equality[*rhs];
            if lhs_prem != rhs_prem {
                flat_atoms.push(FlatAtom::Equal(lhs_prem, rhs_prem));
            }
        },
        Defined(_, _) => panic!("Not implemented"),
        Predicate(name, args) => {
            let pred_args = args.iter().copied().map(|arg| premise_equality[arg]).collect();
            flat_atoms.push(FlatAtom::Relation(name.clone(), pred_args));
        },
    }
    flat_atoms
}

fn flatten_formula(
    universe: &TermUniverse,
    premise_equality: &PremiseEquality,
    first_structural_occurence: &IdValMap<Term, bool>,
    formula: &Formula,
) -> Vec<FlatAtom> {
    let mut flat_formula = Vec::new();
    for atom in formula.atoms.iter() {
        flat_formula.extend(flatten_atom(universe, premise_equality, first_structural_occurence, atom));
    }
    flat_formula
}

//fn flat_premise(
//    sequent: &Sequent,
//    analysis: &SequentAnalysis,
//) -> Vec<FlatAtom> {
//    let universe = &sequent.universe;
//    let premise_equality = &analysis.premise_equality;
//    let first_structural_occurence = &analysis.first_structural_occurence;
//
//    let mut flat_prem: Vec<FlatAtom> = Vec::new();
//    use SequentData::*;
//    let premise_atoms_terms_end = match &sequent.data {
//        SurjectiveImplication(prem, _) | GeneralImplication(prem, _) | ConditionalReduction(prem, _, _) => {
//            for atom in prem.0.iter() {
//                flat_prem.extend(flatten_atom(universe, premise_equality, first_structural_occurence, atom));
//            }
//            prem.0.last().map(|last_atom| last_atom.terms_end).unwrap_or(Term(0))
//        },
//        Reduction(_, _) => Term(0),
//    };
//
//    match &sequent.data {
//        SurjectiveImplication(_, _) | GeneralImplication(_, _) => (),
//        Reduction(from, _) | ConditionalReduction(_, from, _) => {
//            debug_assert_eq!(*from, sequent.first_conclusion_term);
//            for tm in (premise_atoms_terms_end.0 .. from.0).map(Term) {
//                flat_prem.extend(flatten_term(universe, premise_equality, first_structural_occurence, tm));
//            }
//        },
//    }
//
//    flat_prem
//}
//
//fn flat_conclusion(
//    sequent: &Sequent,
//    analysis: &SequentAnalysis,
//) -> Vec<FlatAtom> {
//    let universe = &sequent.universe;
//    let prem_eq = &analysis.premise_equality;
//    let first_occ = &analysis.first_structural_occurence;
//
//    let mut flat_conc: Vec<FlatAtom> = Vec::new();
//    use SequentData::*;
//    match &sequent.data {
//        SurjectiveImplication(_, conc) | GeneralImplication(_, conc) => {
//            for atom in conc.0.iter() {
//                flat_conc.extend(flatten_atom(universe, prem_eq, first_occ, atom));
//            }
//        },
//        Reduction(from, to) | ConditionalReduction(_, from, to) => {
//            use TermData::*;
//            match universe.data(*from) {
//                Variable(_) | Wildcard => panic!("Reduction from variable or wildcard not supported"),
//                Application(name, args) => {
//                    let rel_args: Vec<FlatTerm> =
//                        args.iter().copied()
//                        .chain(once(*to)).map(|tm| prem_eq[tm])
//                        .collect();
//                    flat_conc.push(FlatAtom::Relation(name.clone(), rel_args));
//                },
//            }
//        },
//    }
//
//    flat_conc
//}
//
//fn flatten_sequent(
//    sequent: &Sequent,
//    analysis: &SequentAnalysis,
//) -> FlatSequent {
//    FlatSequent {
//        premise: flat_premise(sequent, analysis),
//        conclusion: flat_conclusion(sequent, analysis),
//    }
//}
//
//#[cfg(test)]
//mod tests {
//
//use super::*;
//use indoc::indoc;
//use crate::grammar::TheoryParser;
//
//#[test]
//fn simple_reduction() {
//    let src = indoc! {"
//        Sort mor;
//        Func comp : mor * mor -> mor;
//        Axiom comp(h, comp(g, f)) ~> comp(comp(h, g), f);
//    "};
//    let (sig, axioms) = TheoryParser::new().parse(src).unwrap();
//
//    let comp = || { "comp".to_string() };
//    let (seq, ana) = &axioms[0];
//    let prem_eq = &ana.premise_equality;
//
//    let h = prem_eq[Term(0)];
//    let g = prem_eq[Term(1)];
//    let f = prem_eq[Term(2)];
//    let gf = prem_eq[Term(3)];
//    let hg = prem_eq[Term(6)];
//    let hg_f = prem_eq[Term(8)];
//    let h_gf = prem_eq[Term(9)];
//
//    let premise = vec![
//        FlatAtom::Relation(comp(), vec![g, f, gf]),
//        FlatAtom::Relation(comp(), vec![h, g, hg]),
//        FlatAtom::Relation(comp(), vec![hg, f, hg_f]),
//    ];
//    let conclusion = vec![
//        FlatAtom::Relation(comp(), vec![h, gf, hg_f]),
//    ];
//
//    assert_eq!(flatten_sequent(seq, ana), FlatSequent{premise, conclusion});
//}
//
//#[test]
//fn general_implication() {
//    let src = indoc! {"
//        Sort obj;
//        Sort mor;
//
//        Func comp : mor * mor -> mor;
//        Pred signature: obj * mor * obj;
//
//        Axiom signature(x, f, y) & signature(y, g, z) => signature(x, comp(g, f), z);
//    "};
//    let (sig, axioms) = TheoryParser::new().parse(src).unwrap();
//
//    let comp = || { "comp".to_string() };
//    let signature = || { "signature".to_string() };
//    let (seq, ana) = &axioms[0];
//    let prem_eq = &ana.premise_equality;
//
//    let x = prem_eq[Term(0)];
//    let f = prem_eq[Term(1)];
//    let y = prem_eq[Term(2)];
//    let g = prem_eq[Term(4)];
//    let z = prem_eq[Term(5)];
//    let gf = prem_eq[Term(9)];
//
//    let premise = vec![
//        FlatAtom::Relation(signature(), vec![x, f, y]),
//        FlatAtom::Relation(signature(), vec![y, g, z]),
//    ];
//    let conclusion = vec![
//        FlatAtom::Relation(comp(), vec![g, f, gf]),
//        FlatAtom::Relation(signature(), vec![x, gf, z]),
//    ];
//
//    assert_eq!(flatten_sequent(seq, ana), FlatSequent{premise, conclusion});
//}
//
//#[test]
//fn surjective_implication() {
//    let src = indoc!{"
//        Sort obj;
//        Sort mor;
//
//        Func comp : mor * mor -> mor;
//        Func id : obj -> mor;
//
//        Axiom g = comp(f, id(_)) => f = g;
//    "};
//    let (sig, axioms) = TheoryParser::new().parse(src).unwrap();
//
//    let comp = || { "comp".to_string() };
//    let id = || { "id".to_string() };
//    let (seq, ana) = &axioms[0];
//    let prem_eq = &ana.premise_equality;
//
//    let g_fi = prem_eq[Term(0)];
//    let f = prem_eq[Term(1)];
//    let wc = prem_eq[Term(2)];
//    let i = prem_eq[Term(3)];
//
//    let premise = vec![
//        FlatAtom::Relation(id(), vec![wc, i]),
//        FlatAtom::Relation(comp(), vec![f, i, g_fi]),
//    ];
//    let conclusion = vec![
//        FlatAtom::Equal(f, g_fi),
//    ];
//
//    assert_eq!(flatten_sequent(seq, ana), FlatSequent{premise, conclusion});
//}
//
//}
