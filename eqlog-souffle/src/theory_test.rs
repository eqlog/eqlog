use super::*;
use indoc::indoc;

use crate::grammar::TheoryParser;
use crate::ast::*;

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

    use Sequent::*;
    use Term::*;

    assert_eq!(*th.sorts(), hashmap!{obj() => Sort(obj()), mor() => Sort(mor())});

    let f = || { Variable("f".to_string()) };
    let g = || { Variable("g".to_string()) };
    let h = || { Variable("h".to_string()) };
    let x = || { Variable("x".to_string()) };
    let y = || { Variable("y".to_string()) };
    let z = || { Variable("z".to_string()) };
    let axiom_sequents: Vec<Sequent> =
        th.axioms().iter()
        .map(|si| (*si.sequent()).clone())
        .collect();
    assert_eq!(axiom_sequents.len(), 3);
    assert_eq!(
        axiom_sequents[0],
        Reduction(
            Application(comp(), vec![h(), Application(comp(), vec![g(), f()])]),
            Application(comp(), vec![Application(comp(), vec![h(), g()]), f()])
        ),
    );
    assert_eq!(
        axiom_sequents[1],
        GeneralImplication(
            Formula(vec![
                Atom::Predicate(signature(), vec![x(), f(), y()]),
                Atom::Predicate(signature(), vec![y(), g(), z()])
            ]),
            Formula(vec![
                Atom::Predicate(signature(), vec![x(), Application(comp(), vec![g(), f()]), z()]),
            ])
        ),
    );

    for seq in th.axioms().iter().map(|a| a.sequent()) {
        seq.for_each_subterm(|tm| {
            match tm {
                Application(c, args) => {
                    match c.as_str() {
                        "comp" => assert_eq!(args.len(), 2),
                        "id" => assert_eq!(args.len(), 1),
                        _ => panic!(),
                    };
                },
                _ => {},
            };
        });
    }

    let (from, to) = match th.axioms()[0].sequent() {
        Reduction(from, to) => (from, to),
        _ => panic!(),
    };
    let (h0, g0f0) = match from {
        Application(_, args) => (&args[0], &args[1]),
        _ => panic!(),
    };
    let (g0, f0) = match g0f0 {
        Application(_, args) => (&args[0], &args[1]),
        _ => panic!(),
    };
    let (h1g1, f1) = match to {
        Application(_, args) => (&args[0], &args[1]),
        _ => panic!(),
    };
    let (h1, g1) = match h1g1 {
        Application(_, args) => (&args[0], &args[1]),
        _ => panic!(),
    };

    let si = &th.axioms()[0];
    assert_eq!(si.term_index(f0).unwrap(), si.term_index(f1).unwrap());
    assert_eq!(si.term_index(g0).unwrap(), si.term_index(g1).unwrap());
    assert_eq!(si.term_index(h0).unwrap(), si.term_index(h1).unwrap());

    assert_eq!(si.term_sort(f0).unwrap(), mor());
    assert_eq!(si.term_sort(g0).unwrap(), mor());
    assert_eq!(si.term_sort(h0).unwrap(), mor());

    let (prem, conc) = match th.axioms()[1].sequent() {
        GeneralImplication(Formula(prem), Formula(to)) => (prem, to),
        _ => panic!(),
    };
    assert_eq!(prem.len(), 2);
    assert_eq!(conc.len(), 1);
    let sigf = &prem[0];
    let sigg = &prem[1];
    let siggf = &conc[0];
    for atom in &[sigf, sigg, siggf] {
        match atom {
            Atom::Predicate(p, args) => {
                assert_eq!(p, &signature());
                assert_eq!(args.len(), 3);
            },
            _ => panic!(),
        };
    }
    let (x0, f0, y0) = match sigf {
        Atom::Predicate(_, args) => (&args[0], &args[1], &args[2]),
        _ => panic!(),
    };
    let (y1, g0, z0) = match sigg {
        Atom::Predicate(_, args) => (&args[0], &args[1], &args[2]),
        _ => panic!(),
    };
    let (x1, gf, z1) = match siggf {
        Atom::Predicate(_, args) => (&args[0], &args[1], &args[2]),
        _ => panic!(),
    };
    let (g1, f1) = match gf {
        Application(_, args) => (&args[0], &args[1]),
        _ => panic!(),
    };

    let si = &th.axioms()[1];
    assert_eq!(si.term_index(x0).unwrap(), si.term_index(x1).unwrap());
    assert_eq!(si.term_index(y0).unwrap(), si.term_index(y1).unwrap());
    assert_eq!(si.term_index(z0).unwrap(), si.term_index(z1).unwrap());
    assert_eq!(si.term_index(f0).unwrap(), si.term_index(f1).unwrap());
    assert_eq!(si.term_index(g0).unwrap(), si.term_index(g1).unwrap());

    assert_eq!(si.term_sort(x0).unwrap(), obj());
    assert_eq!(si.term_sort(y0).unwrap(), obj());
    assert_eq!(si.term_sort(z0).unwrap(), obj());
    assert_eq!(si.term_sort(f0).unwrap(), mor());
    assert_eq!(si.term_sort(g0).unwrap(), mor());

    let (prem, conc) = match th.axioms()[2].sequent() {
        SurjectiveImplication(Formula(prem), Formula(to)) => (prem, to),
        _ => panic!(),
    };
    assert_eq!(prem.len(), 1);
    assert_eq!(conc.len(), 1);
    let (g0, f_id) = match &prem[0] {
        Atom::Equal(lhs, rhs) => (lhs, rhs),
        _ => panic!(),
    };
    let (f0, id_wildcard) = match f_id {
        Application(_, args) => (&args[0], &args[1]),
        _ => panic!(),
    };
    let wc = match id_wildcard {
        Application(_, args) => &args[0],
        _ => panic!(),
    };
    match wc {
        Wildcard(Some(_)) => (),
        _ => panic!(),
    };
    let (f1, g1) = match &conc[0] {
        Atom::Equal(lhs, rhs) => (lhs, rhs),
        _ => panic!(),
    };

    let si = &th.axioms()[2];
    assert_eq!(si.term_index(f0).unwrap(), si.term_index(f1).unwrap());
    assert_eq!(si.term_index(g0).unwrap(), si.term_index(g1).unwrap());

    assert_eq!(si.term_sort(wc).unwrap(), obj());
    assert_eq!(si.term_sort(f0).unwrap(), mor());
    assert_eq!(si.term_sort(g0).unwrap(), mor());
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
