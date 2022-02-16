use super::*;
use indoc::indoc;

use crate::grammar::TheoryParser;
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

    let axioms: Vec<Sequent> = th.axioms().iter().map(|si| si.sequent.clone()).collect();
    let (ax0, ax1, ax2) = match axioms.as_slice() {
        [ax0, ax1, ax2] => (ax0, ax1, ax2),
        _ => panic!("{}", axioms.len()),
    };

    {
        let mut universe = TermUniverse::new();
        let h0 = universe.new_term(h());
        let g0 = universe.new_term(g());
        let f0 = universe.new_term(f());
        let gf = universe.new_term(Application(comp(), vec![g0, f0]));
        let h_gf = universe.new_term(Application(comp(), vec![h0, gf]));

        let h1 = universe.new_term(h());
        let g1 = universe.new_term(g());
        let hg = universe.new_term(Application(comp(), vec![h1, g1]));
        let f1 = universe.new_term(f());
        let hg_f = universe.new_term(Application(comp(), vec![hg, f1]));

        let data = SequentData::Reduction(h_gf, hg_f);
        assert_eq!(ax0, &Sequent{universe, data});
    }

    {
        let mut universe = TermUniverse::new();
        let x0 = universe.new_term(x());
        let f0 = universe.new_term(f());
        let y0 = universe.new_term(y());
        let sig_f = Atom::Predicate(signature(), vec![x0, f0, y0]);

        let y1 = universe.new_term(y());
        let g0 = universe.new_term(g());
        let z0 = universe.new_term(z());
        let sig_g = Atom::Predicate(signature(), vec![y1, g0, z0]);

        let x1 = universe.new_term(x());
        let g1 = universe.new_term(g());
        let f1 = universe.new_term(f());
        let gf = universe.new_term(Application(comp(), vec![g1, f1]));
        let z1 = universe.new_term(z());
        let sig_gf = Atom::Predicate(signature(), vec![x1, gf, z1]);

        let data = SequentData::GeneralImplication(
            Formula(vec![sig_f, sig_g]),
            Formula(vec![sig_gf])
        );
        assert_eq!(ax1, &Sequent{universe, data});
    }

    {
        let mut universe = TermUniverse::new();
        let g0 = universe.new_term(g());
        let f0 = universe.new_term(f());
        let wc = universe.new_term(Wildcard);
        let i = universe.new_term(Application(id(), vec![wc]));
        let fi = universe.new_term(Application(comp(), vec![f0, i]));
        let prem_eq = Atom::Equal(g0, fi);

        let f1 = universe.new_term(f());
        let g1 = universe.new_term(g());
        let conc_eq = Atom::Equal(f1, g1);
        let data = SequentData::SurjectiveImplication(
            Formula(vec![prem_eq]),
            Formula(vec![conc_eq])
        );
        assert_eq!(ax2, &Sequent{universe, data});
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
