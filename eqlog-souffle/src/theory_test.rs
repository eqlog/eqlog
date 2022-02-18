use super::*;
use indoc::indoc;

use crate::grammar::TheoryParser;
use crate::theory::*;
use crate::indirect_ast::*;

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
    let th = TheoryParser::new().parse(src).unwrap();
    let obj = || { "obj".to_string() };
    let mor = || { "mor".to_string() };
    let comp = || { "comp".to_string() };
    let id = || { "id".to_string() };
    let signature = || { "signature".to_string() };

    assert_eq!(
        *th.sorts(),
        hashmap!{
            obj() => Sort(obj()),
            mor() => Sort(mor()),
        }
    );
    assert_eq!(
        *th.functions(),
        hashmap!{
            comp() => Function{name: comp(), dom: vec![mor(), mor()], cod: mor()},
            id() => Function{name: id(), dom: vec![obj()], cod: mor()},
        }
    );
    assert_eq!(
        *th.predicates(),
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

    let axioms: Vec<AnalyzedSequent> = th.axioms().iter().cloned().collect();
    let (ax0, ax1, ax2) = match axioms.as_slice() {
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
        assert_eq!(ax0.sequent, Sequent{universe, data});
        assert_eq!(ax0.premise_terms, premise_terms);

        assert_eq!(ax0.structural_equality[f0.0], ax0.structural_equality[f1.0]);
        assert_eq!(ax0.structural_equality[g0.0], ax0.structural_equality[g1.0]);
        assert_eq!(ax0.structural_equality[h0.0], ax0.structural_equality[h1.0]);

        assert_eq!(ax0.premise_equality, ax0.structural_equality);
        assert_eq!(ax0.conclusion_equality[h_gf.0], ax0.conclusion_equality[hg_f.0]);

        assert_eq!(ax0.sorts[ax0.conclusion_equality[f0.0]], mor());
        assert_eq!(ax0.sorts[ax0.conclusion_equality[g0.0]], mor());
        assert_eq!(ax0.sorts[ax0.conclusion_equality[h0.0]], mor());
        assert_eq!(ax0.sorts[ax0.conclusion_equality[hg.0]], mor());
        assert_eq!(ax0.sorts[ax0.conclusion_equality[gf.0]], mor());
        assert_eq!(ax0.sorts[ax0.conclusion_equality[h_gf.0]], mor());
        assert_eq!(ax0.sorts[ax0.conclusion_equality[hg_f.0]], mor());
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
        assert_eq!(ax1.sequent, Sequent{universe, data});
        assert_eq!(ax1.premise_terms, premise_terms);

        assert_eq!(ax1.structural_equality[f0.0], ax1.structural_equality[f1.0]);
        assert_eq!(ax1.structural_equality[g0.0], ax1.structural_equality[g1.0]);
        assert_eq!(ax1.structural_equality[x0.0], ax1.structural_equality[x1.0]);
        assert_eq!(ax1.structural_equality[y0.0], ax1.structural_equality[y1.0]);
        assert_eq!(ax1.structural_equality[z0.0], ax1.structural_equality[z1.0]);

        assert_eq!(ax1.structural_equality, ax1.premise_equality);
        assert_eq!(ax1.structural_equality, ax1.conclusion_equality);

        assert_eq!(ax1.sorts[ax1.conclusion_equality[x0.0]], obj());
        assert_eq!(ax1.sorts[ax1.conclusion_equality[y0.0]], obj());
        assert_eq!(ax1.sorts[ax1.conclusion_equality[z0.0]], obj());
        assert_eq!(ax1.sorts[ax1.conclusion_equality[f0.0]], mor());
        assert_eq!(ax1.sorts[ax1.conclusion_equality[g0.0]], mor());
        assert_eq!(ax1.sorts[ax1.conclusion_equality[gf.0]], mor());
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
        assert_eq!(ax2.sequent, Sequent{universe, data});
        assert_eq!(ax2.premise_terms, premise_terms);

        assert_eq!(ax2.structural_equality[f0.0], ax2.structural_equality[f1.0]);
        assert_eq!(ax2.structural_equality[g0.0], ax2.structural_equality[g1.0]);
        assert_eq!(ax2.premise_equality[g0.0], ax2.premise_equality[fi.0]);
        assert_ne!(ax2.premise_equality[f1.0], ax2.premise_equality[g1.0]);
        assert_eq!(ax2.conclusion_equality[f1.0], ax2.conclusion_equality[g1.0]);

        assert_eq!(ax2.sorts[ax2.conclusion_equality[f0.0]], mor());
        assert_eq!(ax2.sorts[ax2.conclusion_equality[g0.0]], mor());
        assert_eq!(ax2.sorts[ax2.conclusion_equality[i.0]], mor());
        assert_eq!(ax2.sorts[ax2.conclusion_equality[fi.0]], mor());
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
