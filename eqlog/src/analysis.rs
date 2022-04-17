use crate::ast::*;
use crate::error::*;
use crate::signature::*;
use crate::unification::{TermMap, TermUnification};
use convert_case::{Case, Casing};
use std::collections::{HashMap, HashSet};

pub fn infer_sorts(
    signature: &Signature,
    sequent: &Sequent,
) -> Result<TermMap<String>, CompileError> {
    let unify_sorts = |mut lhs: HashSet<String>, rhs: HashSet<String>| {
        lhs.extend(rhs);
        lhs
    };

    let mut unification = TermUnification::new(
        &sequent.universe,
        vec![HashSet::new(); sequent.universe.len()],
        unify_sorts,
    );
    // Merge variables of the same name.
    unification.congruence_closure();

    // Assign sorts based on application of functions.
    for tm in sequent.universe.iter_terms() {
        match sequent.universe.data(tm) {
            TermData::Application(f, args) => {
                let loc = sequent.universe.location(tm);
                let Function { dom, cod, .. } = signature.get_function_at(f, loc)?;
                if args.len() != dom.len() {
                    return Err(CompileError::FunctionArgumentNumber {
                        function: f.clone(),
                        expected: dom.len(),
                        got: args.len(),
                        location: sequent.universe.location(tm),
                    });
                }
                for (arg, sort) in args.iter().copied().zip(dom) {
                    unification[arg].insert(sort.clone());
                }
                unification[tm].insert(cod.clone());
            }
            TermData::Wildcard | TermData::Variable(_) => (),
        }
    }

    // Assign sorts based on atoms.
    for atom in sequent.premise.iter().chain(sequent.conclusion.iter()) {
        match &atom.data {
            AtomData::Equal(lhs, rhs) => {
                unification.union(*lhs, *rhs);
            }
            AtomData::Defined(tm, Some(sort)) => {
                unification[*tm].insert(sort.clone());
            }
            AtomData::Defined(_, None) => (),
            AtomData::Predicate(p, args) => {
                let Predicate { arity, .. } = signature.get_predicate_at(p, atom.location)?;
                if args.len() != arity.len() {
                    return Err(CompileError::PredicateArgumentNumber {
                        predicate: p.clone(),
                        expected: arity.len(),
                        got: args.len(),
                        location: atom.location,
                    });
                }
                for (arg, sort) in args.iter().copied().zip(arity) {
                    unification[arg].insert(sort.clone());
                }
            }
        }
    }

    // Check that all terms have precisely one assigned sort.
    for tm in sequent.universe.iter_terms() {
        match unification[tm].len() {
            0 => {
                return Err(CompileError::NoSort {
                    location: sequent.universe.location(tm),
                })
            }
            1 => (),
            _ => {
                return Err(CompileError::ConflictingSorts {
                    location: sequent.universe.location(tm),
                    sorts: unification[tm].iter().cloned().collect(),
                })
            }
        }
    }

    let sorts = unification
        .freeze()
        .map(|sorts| sorts.into_iter().next().unwrap());
    Ok(sorts)
}

pub fn check_epimorphism(sequent: &Sequent) -> Result<(), CompileError> {
    let universe = &sequent.universe;
    let mut has_occurred = TermUnification::new(
        universe,
        vec![false; universe.len()],
        |lhs_occured, rhs_occured| lhs_occured || rhs_occured,
    );

    // Set all premise terms to have occurred.
    for tm in sequent
        .premise
        .iter()
        .map(|atom| atom.iter_subterms(universe))
        .flatten()
    {
        has_occurred[tm] = true;
    }

    // Unify terms occuring in equalities in premise.
    for atom in &sequent.premise {
        use AtomData::*;
        match &atom.data {
            Equal(lhs, rhs) => {
                has_occurred.union(*lhs, *rhs);
            }
            Defined(_, _) | Predicate(_, _) => (),
        }
    }

    has_occurred.congruence_closure();

    // Check that conclusion doesn't contain wildcards or variables that haven't occurred in
    // premise.
    for tm in sequent
        .conclusion
        .iter()
        .map(|atom| atom.iter_subterms(universe))
        .flatten()
    {
        match universe.data(tm) {
            TermData::Variable(_) | TermData::Wildcard if has_occurred[tm] => (),
            TermData::Application(_, _) => (),
            TermData::Variable(var) => {
                return Err(CompileError::VariableNotInPremise {
                    var: var.clone(),
                    location: universe.location(tm),
                })
            }
            TermData::Wildcard => {
                return Err(CompileError::WildcardInConclusion {
                    location: universe.location(tm),
                })
            }
        }
    }

    for atom in &sequent.conclusion {
        use AtomData::*;
        match &atom.data {
            Equal(lhs, rhs) => {
                let lhs = *lhs;
                let rhs = *rhs;
                if !has_occurred[lhs] && !has_occurred[rhs] {
                    return Err(CompileError::ConclusionEqualityOfNewTerms {
                        location: atom.location,
                    });
                }

                if !has_occurred[lhs] || !has_occurred[rhs] {
                    let new = if has_occurred[lhs] { rhs } else { lhs };
                    use TermData::*;
                    match universe.data(new) {
                        Variable(_) | Wildcard => {
                            // Variables or Wildcards should've been checked earlier.
                            debug_assert!(has_occurred[new]);
                        }
                        Application(_, args) => {
                            if let Some(arg) = args.iter().find(|arg| !has_occurred[**arg]) {
                                return Err(CompileError::ConclusionEqualityArgNew {
                                    location: universe.location(*arg),
                                });
                            }
                        }
                    }
                }

                has_occurred.union(lhs, rhs);
                has_occurred.congruence_closure();
            }
            Defined(_, _) => (),
            Predicate(_, args) => {
                if let Some(arg) = args.iter().copied().find(|arg| !has_occurred[*arg]) {
                    return Err(CompileError::ConclusionPredicateArgNew {
                        location: universe.location(arg),
                    });
                }
            }
        }
        for tm in atom.iter_subterms(universe) {
            has_occurred[tm] = true;
        }
    }

    Ok(())
}

pub fn check_variable_case(sequent: &Sequent) -> Result<(), CompileError> {
    for tm in sequent.universe.iter_terms() {
        if let TermData::Variable(v) = sequent.universe.data(tm) {
            if *v != v.to_case(Case::Snake) {
                return Err(CompileError::VariableNotSnakeCase {
                    name: v.into(),
                    location: sequent.universe.location(tm),
                });
            }
        }
    }
    Ok(())
}

pub fn check_variable_occurence(sequent: &Sequent) -> Result<(), CompileError> {
    let mut occ_nums: HashMap<&str, (usize, Option<Location>)> = HashMap::new();
    for tm in sequent.universe.iter_terms() {
        if let TermData::Variable(v) = sequent.universe.data(tm) {
            if let Some((n, _)) = occ_nums.get_mut(v.as_str()) {
                *n += 1;
            } else {
                let loc = sequent.universe.location(tm);
                occ_nums.insert(v, (1, loc));
            }
        }
    }
    for (name, (n, location)) in occ_nums.into_iter() {
        if n == 1 {
            return Err(CompileError::VariableOccursOnlyOnce {
                name: name.into(),
                location,
            });
        }
    }
    Ok(())
}

pub fn check_semantically(
    signature: &Signature,
    sequent: &Sequent,
) -> Result<TermMap<String>, CompileError> {
    let sorts = infer_sorts(signature, sequent)?;
    check_epimorphism(sequent)?;
    check_variable_case(sequent)?;
    check_variable_occurence(sequent)?;
    Ok(sorts)
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::grammar::TheoryParser;
    use indoc::indoc;
    use regex::Regex;
    use std::collections::BTreeSet;

    fn src_loc(s: &str, n: usize, src: &str) -> Location {
        let re = Regex::new(
            &s.replace("(", "\\(")
                .replace(")", "\\)")
                .replace(".", "\\.")
                .replace("*", "\\*"),
        )
        .unwrap();
        let m = re.find_iter(src).nth(n).unwrap();
        Location(m.start(), m.end())
    }

    #[test]
    fn good_theory() {
        let src = indoc! {"
            Sort Obj;
            Sort Mor;

            Func Comp : Mor * Mor -> Mor;
            Axiom Comp(h, Comp(g, f)) ~> Comp(Comp(h, g), f);

            Pred Signature: Obj * Mor * Obj;

            Axiom Signature(x, f, y) & Signature(y, g, z) => Comp(g, f)! & Signature(x, Comp(g, f), z);

            Func Id : Obj -> Mor; Axiom g = Comp(f, Id(_)) => f = g;
        "};
        let src_loc = |s: &str, n: usize| -> Location { src_loc(s, n, src) };
        let (sig, axioms) = TheoryParser::new()
            .parse(&mut TermUniverse::new(), src)
            .unwrap();
        let obj = || "Obj".to_string();
        let mor = || "Mor".to_string();
        let comp = || "Comp".to_string();
        let id = || "Id".to_string();
        let signature = || "Signature".to_string();

        assert_eq!(
            sig.iter_sorts()
                .map(|sort| sort.name.clone())
                .collect::<BTreeSet<String>>(),
            btreeset! {obj(), mor()}
        );
        let obj_sort = sig.iter_sorts().find(|sort| sort.name == obj()).unwrap();
        let mor_sort = sig.iter_sorts().find(|sort| sort.name == mor()).unwrap();

        assert_eq!(
            sig.iter_predicates()
                .map(|p| p.name.clone())
                .collect::<BTreeSet<String>>(),
            btreeset! {signature()}
        );
        let signature_pred = sig
            .iter_predicates()
            .find(|p| p.name == signature())
            .unwrap();

        assert_eq!(
            sig.iter_functions()
                .map(|f| f.name.clone())
                .collect::<BTreeSet<String>>(),
            btreeset! {comp(), id()}
        );
        let id_func = sig.iter_functions().find(|f| f.name == id()).unwrap();
        let comp_func = sig.iter_functions().find(|f| f.name == comp()).unwrap();

        assert_eq!(obj_sort.location, Some(src_loc("Sort Obj;", 0)));
        assert_eq!(obj_sort.location, Some(src_loc("Sort Obj;", 0)));
        assert_eq!(mor_sort.location, Some(src_loc("Sort Mor;", 0)));
        assert_eq!(
            signature_pred.location,
            Some(src_loc("Pred Signature: Obj * Mor * Obj;", 0))
        );
        assert_eq!(id_func.location, Some(src_loc("Func Id : Obj -> Mor;", 0)));
        assert_eq!(
            comp_func.location,
            Some(src_loc("Func Comp : Mor * Mor -> Mor;", 0))
        );

        assert_eq!(obj_sort.name, obj());
        assert_eq!(mor_sort.name, mor());

        assert_eq!(signature_pred.name, signature());
        assert_eq!(signature_pred.arity, vec![obj(), mor(), obj()]);

        assert_eq!(id_func.name, id());
        assert_eq!(id_func.dom, vec![obj()]);
        assert_eq!(id_func.cod, mor());
        assert_eq!(comp_func.name, comp());
        assert_eq!(comp_func.dom, vec![mor(), mor()]);
        assert_eq!(comp_func.cod, mor());

        use TermData::*;
        let f = || Variable("f".to_string());
        let g = || Variable("g".to_string());
        let h = || Variable("h".to_string());
        let x = || Variable("x".to_string());
        let y = || Variable("y".to_string());
        let z = || Variable("z".to_string());

        let (ax0, ax1, ax2) = match axioms.as_slice() {
            [ax0, ax1, ax2] => (ax0, ax1, ax2),
            _ => {
                assert_eq!(axioms.len(), 3);
                panic!()
            }
        };

        {
            let (Axiom { sequent: seq, .. }, sorts) = ax0;
            let mut universe = TermUniverse::new();

            // Comp(h, Comp(g, f))
            let h0 = universe.new_term(h(), None);
            assert_eq!(seq.universe.location(h0), Some(src_loc("h", 0)));
            let g0 = universe.new_term(g(), None);
            assert_eq!(seq.universe.location(g0), Some(src_loc("g", 0)));
            let f0 = universe.new_term(f(), None);
            assert_eq!(seq.universe.location(f0), Some(src_loc("f", 0)));
            let gf = universe.new_term(Application(comp(), vec![g0, f0]), None);
            assert_eq!(seq.universe.location(gf), Some(src_loc("Comp(g, f)", 0)));
            let h_gf = universe.new_term(Application(comp(), vec![h0, gf]), None);
            assert_eq!(
                seq.universe.location(h_gf),
                Some(src_loc("Comp(h, Comp(g, f))", 0))
            );

            // Comp(Comp(h, g), f)
            let h1 = universe.new_term(h(), None);
            assert_eq!(seq.universe.location(h1), Some(src_loc("h", 1)));
            let g1 = universe.new_term(g(), None);
            assert_eq!(seq.universe.location(g1), Some(src_loc("g", 1)));
            let hg = universe.new_term(Application(comp(), vec![h1, g1]), None);
            assert_eq!(seq.universe.location(hg), Some(src_loc("Comp(h, g)", 0)));
            let f1 = universe.new_term(f(), None);
            assert_eq!(seq.universe.location(f1), Some(src_loc("f", 1)));
            let hg_f = universe.new_term(Application(comp(), vec![hg, f1]), None);
            assert_eq!(
                seq.universe.location(hg_f),
                Some(src_loc("Comp(Comp(h, g), f)", 0))
            );

            let premise = vec![
                Atom {
                    data: AtomData::Defined(h0, None),
                    location: None,
                },
                Atom {
                    data: AtomData::Defined(gf, None),
                    location: None,
                },
                Atom {
                    data: AtomData::Defined(hg_f, None),
                    location: None,
                },
            ];

            let conclusion = vec![Atom {
                data: AtomData::Equal(h_gf, hg_f),
                location: None,
            }];

            assert_eq!(seq.universe.without_locations(), universe);
            assert_eq!(seq.premise, premise);
            assert_eq!(seq.conclusion, conclusion);

            assert_eq!(sorts[f0], mor());
            assert_eq!(sorts[g0], mor());
            assert_eq!(sorts[h0], mor());
            assert_eq!(sorts[hg], mor());
            assert_eq!(sorts[gf], mor());
            assert_eq!(sorts[h_gf], mor());
            assert_eq!(sorts[hg_f], mor());
        }

        {
            let (Axiom { sequent: seq, .. }, sorts) = ax1;
            let mut universe = TermUniverse::new();

            let x0 = universe.new_term(x(), None);
            let f0 = universe.new_term(f(), None);
            let y0 = universe.new_term(y(), None);

            let y1 = universe.new_term(y(), None);
            let g0 = universe.new_term(g(), None);
            let z0 = universe.new_term(z(), None);

            let g1 = universe.new_term(g(), None);
            let f1 = universe.new_term(f(), None);
            let gf0 = universe.new_term(Application(comp(), vec![g1, f1]), None);

            let x1 = universe.new_term(x(), None);
            let g2 = universe.new_term(g(), None);
            let f2 = universe.new_term(f(), None);
            let gf1 = universe.new_term(Application(comp(), vec![g2, f2]), None);
            let z1 = universe.new_term(z(), None);

            let premise = vec![
                Atom {
                    data: AtomData::Predicate(signature(), vec![x0, f0, y0]),
                    location: None,
                },
                Atom {
                    data: AtomData::Predicate(signature(), vec![y1, g0, z0]),
                    location: None,
                },
            ];
            assert_eq!(
                seq.premise[0].location,
                Some(src_loc("Signature(x, f, y)", 0))
            );
            assert_eq!(
                seq.premise[1].location,
                Some(src_loc("Signature(y, g, z)", 0))
            );

            let conclusion = vec![
                Atom {
                    data: AtomData::Defined(gf0, None),
                    location: None,
                },
                Atom {
                    data: AtomData::Predicate(signature(), vec![x1, gf1, z1]),
                    location: None,
                },
            ];
            assert_eq!(seq.conclusion[0].location, Some(src_loc("Comp(g, f)!", 0)));
            assert_eq!(
                seq.conclusion[1].location,
                Some(src_loc("Signature(x, Comp(g, f), z)", 0))
            );

            assert_eq!(
                seq.without_locations(),
                Sequent {
                    universe,
                    premise,
                    conclusion
                }
            );

            assert_eq!(sorts[x0], obj());
            assert_eq!(sorts[x1], obj());
            assert_eq!(sorts[y0], obj());
            assert_eq!(sorts[y1], obj());
            assert_eq!(sorts[z0], obj());
            assert_eq!(sorts[z1], obj());
            assert_eq!(sorts[f0], mor());
            assert_eq!(sorts[f1], mor());
            assert_eq!(sorts[f2], mor());
            assert_eq!(sorts[g0], mor());
            assert_eq!(sorts[g1], mor());
            assert_eq!(sorts[g2], mor());
            assert_eq!(sorts[gf0], mor());
            assert_eq!(sorts[gf1], mor());
        }

        {
            let (Axiom { sequent: seq, .. }, sorts) = ax2;
            let mut universe = TermUniverse::new();

            let g0 = universe.new_term(g(), None);
            let f0 = universe.new_term(f(), None);
            let wc = universe.new_term(Wildcard, None);
            let i = universe.new_term(Application(id(), vec![wc]), None);
            let fi = universe.new_term(Application(comp(), vec![f0, i]), None);
            let prem_eq = Atom {
                data: AtomData::Equal(g0, fi),
                location: None,
            };

            let f1 = universe.new_term(f(), None);
            let g1 = universe.new_term(g(), None);
            let conc_eq = Atom {
                data: AtomData::Equal(f1, g1),
                location: None,
            };

            let premise = vec![prem_eq];
            let conclusion = vec![conc_eq];

            assert_eq!(
                seq.without_locations(),
                Sequent {
                    universe,
                    premise,
                    conclusion
                }
            );

            assert_eq!(sorts[f0], mor());
            assert_eq!(sorts[f1], mor());
            assert_eq!(sorts[g0], mor());
            assert_eq!(sorts[g1], mor());
            assert_eq!(sorts[i], mor());
            assert_eq!(sorts[fi], mor());
        }
    }

    #[test]
    #[should_panic]
    fn wrong_function_argument_number() {
        let src = indoc! {"
            Sort Mor;
            Func Comp : Mor * Mor -> Mor;
            Axiom Comp(g, f, h) ~> g;
        "};
        TheoryParser::new()
            .parse(&mut TermUniverse::new(), src)
            .unwrap();
    }

    #[test]
    #[should_panic]
    fn conflicting_sorts_equality() {
        let src = indoc! {"
        Sort Obj;
        Sort Mor;
        Func Id : Obj -> Mor;
        Axiom Id(x) = f => x = f;
    "};
        TheoryParser::new()
            .parse(&mut TermUniverse::new(), src)
            .unwrap();
    }

    #[test]
    #[should_panic]
    fn conflicting_sorts_reduction() {
        let src = indoc! {"
        Sort Obj;
        Sort Mor;
        Func Id : Obj -> Mor;
        Axiom Id(x) ~> x;
    "};
        TheoryParser::new()
            .parse(&mut TermUniverse::new(), src)
            .unwrap();
    }

    #[test]
    #[should_panic]
    fn conflicting_sorts_predicate() {
        let src = indoc! {"
        Sort Obj;
        Sort Mor;
        Pred IsId : Mor * Obj;
        Axiom IsId(f, x) => IsId(x, f);
    "};
        TheoryParser::new()
            .parse(&mut TermUniverse::new(), src)
            .unwrap();
    }

    #[test]
    #[should_panic]
    fn non_epi() {
        let src = indoc! {"
        Sort Obj;
        Sort Mor;
        Func Id : Obj -> Mor;
        Axiom Id(x) = f =!> f = g;
    "};
        TheoryParser::new()
            .parse(&mut TermUniverse::new(), src)
            .unwrap();
    }

    #[test]
    #[should_panic]
    fn non_surjective0() {
        let src = indoc! {"
        Sort Obj;
        Sort Mor;
        Pred Signature: Obj * Mor * Obj;
        Func Id : Obj -> Mor;
        Func Comp : Mor * Mor -> Mor;
        Axiom Signature(x, f, _) => Comp(f, Id(x)) = f;
    "};
        TheoryParser::new()
            .parse(&mut TermUniverse::new(), src)
            .unwrap();
    }

    #[test]
    #[should_panic]
    fn non_surjective1() {
        let src = indoc! {"
        Sort Obj;
        Sort Mor;
        Pred Signature: Obj * Mor * Obj;
        Func Id : Obj -> Mor;
        Func Comp : Mor * Mor -> Mor;
        Axiom Signature(x, f, _) => f = Comp(f, Id(x));
    "};
        TheoryParser::new()
            .parse(&mut TermUniverse::new(), src)
            .unwrap();
    }

    #[test]
    #[should_panic]
    fn non_surjective2() {
        let src = indoc! {"
        Sort Obj;
        Sort Mor;
        Func Id : Obj -> Mor;
        Axiom x = y => Id(x) = Id(y);
    "};
        TheoryParser::new()
            .parse(&mut TermUniverse::new(), src)
            .unwrap();
    }

    #[test]
    #[should_panic]
    fn no_sort_inferred() {
        let src = indoc! {"
        Sort Obj;
        Axiom x = y => y = x;
    "};
        TheoryParser::new()
            .parse(&mut TermUniverse::new(), src)
            .unwrap();
    }
}
