use crate::eqlog_util::*;
use crate::flat_ast::*;
use eqlog_eqlog::*;
use maplit::btreeset;
use std::collections::{BTreeMap, BTreeSet};
use std::iter::successors;

pub struct SequentFlattening {
    pub name: Option<String>,
    pub sequent: FlatSequent,
    pub sorts: BTreeMap<FlatTerm, String>,
}

fn iter_grouped_morphisms<'a>(
    rule: RuleDeclNode,
    eqlog: &'a Eqlog,
) -> impl 'a + Iterator<Item = Morphism> {
    successors(eqlog.rule_first_grouped_morphism(rule), |prev| {
        eqlog.next_grouped_morphism(*prev)
    })
}

fn get_flat_term_or_create(el: El, flat_names: &mut BTreeMap<El, BTreeSet<FlatTerm>>) -> FlatTerm {
    let len = flat_names
        .iter()
        .map(|(_, flat_terms)| flat_terms.len())
        .sum();
    let names = flat_names.entry(el).or_insert(btreeset! {FlatTerm(len)});
    *names.iter().next().unwrap()
}

fn flatten_delta(
    morphism: Morphism,
    flat_names: &mut BTreeMap<El, BTreeSet<FlatTerm>>,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> Vec<FlatAtom> {
    let codomain = eqlog.cod(morphism).unwrap();
    let mut atoms: Vec<FlatAtom> = Vec::new();

    for (el0, el1) in iter_in_ker(morphism, eqlog) {
        if !eqlog.are_equal_el(el0, el1) {
            let tm0 = get_flat_term_or_create(el0, flat_names);
            let tm1 = get_flat_term_or_create(el1, flat_names);
            atoms.push(FlatAtom::Equal(tm0, tm1));
        }
    }

    *flat_names = {
        let mut new_flat_names = BTreeMap::new();
        for (el, tms) in flat_names.iter() {
            let img_el = eqlog.map_el(morphism, *el).unwrap();
            for tm in tms {
                new_flat_names
                    .entry(img_el)
                    .or_insert(BTreeSet::new())
                    .insert(*tm);
            }
        }
        new_flat_names
    };

    for (pred, els) in iter_pred_app(codomain, eqlog) {
        if !eqlog.pred_tuple_in_img(morphism, pred, els) {
            let el_terms: Vec<FlatTerm> = el_list_vec(els, eqlog)
                .into_iter()
                .map(|el| get_flat_term_or_create(el, flat_names))
                .collect();
            let pred_ident = eqlog
                .iter_semantic_pred()
                .find_map(|(ident, prd)| eqlog.are_equal_pred(prd, pred).then_some(ident))
                .unwrap();
            let pred_name: String = identifiers.get(&pred_ident).unwrap().to_string();
            atoms.push(FlatAtom::Relation(pred_name, el_terms));
        }
    }

    for (func, args, result) in iter_func_app(codomain, eqlog) {
        if !eqlog.func_app_in_img(morphism, func, args) {
            let arg_terms: Vec<FlatTerm> = el_list_vec(args, eqlog)
                .into_iter()
                .map(|el| get_flat_term_or_create(el, flat_names))
                .collect();
            let result_term = get_flat_term_or_create(result, flat_names);

            let mut tuple = arg_terms;
            tuple.push(result_term);

            let func_ident = eqlog
                .iter_semantic_func()
                .find_map(|(ident, fnc)| eqlog.are_equal_func(fnc, func).then_some(ident))
                .unwrap();
            let func_name: String = identifiers.get(&func_ident).unwrap().to_string();
            atoms.push(FlatAtom::Relation(func_name, tuple));
        }
    }

    for el in iter_els(codomain, eqlog) {
        if !eqlog.el_in_img(morphism, el) && !eqlog.constrained_el(el) {
            let tm = get_flat_term_or_create(el, flat_names);

            let typ = el_type(el, eqlog).unwrap();
            let type_ident = eqlog
                .iter_semantic_type()
                .find_map(|(ident, tp)| eqlog.are_equal_type(tp, typ).then_some(ident))
                .unwrap();
            let type_name: String = identifiers.get(&type_ident).unwrap().to_string();
            atoms.push(FlatAtom::Unconstrained(tm, type_name));
        }
    }

    atoms
}

fn sort_map(
    flat_names: &BTreeMap<El, BTreeSet<FlatTerm>>,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> BTreeMap<FlatTerm, String> {
    flat_names
        .iter()
        .map(|(el, tms)| {
            let typ = el_type(*el, eqlog).unwrap();
            let type_ident = eqlog
                .iter_semantic_type()
                .find_map(|(ident, tp)| eqlog.are_equal_type(tp, typ).then_some(ident))
                .unwrap();
            let type_name: &str = identifiers.get(&type_ident).unwrap().as_str();

            tms.iter().copied().map(|tm| (tm, type_name.to_string()))
        })
        .flatten()
        .collect()
}

/// Sort atoms so that each atom corresponds to an epimorphic delta.
///
/// This is necessary so that we add subterms before terms.
/// Consider this eqlog/PHL then atom:
/// ```eqlog
/// then foo(bar())!;
/// ```
///
/// This might correspond to the following flat/RHL atoms:
/// ```eqlog
/// then bar(tm0);
/// then foo(tm0, tm1);
/// ```
/// but it might also correspond to
/// ```eqlog
/// then foo(tm0, tm1);
/// then bar(tm0);
/// ```
///
/// The second version is bad, since here we're introducing the new flat term `tm0` not as last
/// argument, so we want the first one.
///
/// This function reorders the provided atoms so that we always introduce new flat terms only as
/// last arguments. This must be possible; otherwise the function panics.
fn sort_then_atoms(
    mut atoms: Vec<FlatAtom>,
    premise_flat_terms: BTreeSet<FlatTerm>,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> Vec<FlatAtom> {
    let mut result = Vec::new();
    let mut added_flat_terms = premise_flat_terms;
    while !atoms.is_empty() {
        let before_len = atoms.len();
        atoms = atoms
            .into_iter()
            .filter_map(|atom| {
                let should_add = match &atom {
                    FlatAtom::Equal(lhs, rhs) => {
                        added_flat_terms.contains(lhs) && added_flat_terms.contains(rhs)
                    }
                    FlatAtom::Relation(rel, args) => {
                        let rel_ident = *identifiers
                            .iter()
                            .find_map(|(i, s)| (s == rel).then_some(i))
                            .unwrap();
                        let is_func = eqlog.semantic_func(rel_ident).is_some();
                        let is_pred = eqlog.semantic_pred(rel_ident).is_some();
                        assert!(
                            is_func ^ is_pred,
                            "rel should be either function or relation"
                        );
                        let last_arg_is_ok = is_func
                            || match args.last() {
                                Some(last_arg) => added_flat_terms.contains(last_arg),
                                None => true,
                            };

                        last_arg_is_ok
                            && args[0..args.len().saturating_sub(1)]
                                .iter()
                                .all(|arg| added_flat_terms.contains(arg))
                    }
                    FlatAtom::Unconstrained(_, _) => true,
                };

                if should_add {
                    match &atom {
                        FlatAtom::Equal(lhs, rhs) => {
                            added_flat_terms.insert(*lhs);
                            added_flat_terms.insert(*rhs);
                        }
                        FlatAtom::Relation(_, args) => {
                            added_flat_terms.extend(args);
                        }
                        FlatAtom::Unconstrained(tm, _) => {
                            added_flat_terms.insert(*tm);
                        }
                    }
                    result.push(atom);
                    None
                } else {
                    Some(atom)
                }
            })
            .collect();
        assert!(atoms.len() < before_len);
    }

    result
}

pub fn flatten(
    rule: RuleDeclNode,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> SequentFlattening {
    let name = eqlog
        .rule_name(rule)
        .map(|ident| identifiers.get(&ident).unwrap().to_string());
    let mut premise_flat_terms = BTreeSet::new();
    let mut premise = Vec::new();
    let mut conclusion = Vec::new();
    let mut flat_names = BTreeMap::new();

    let mut grouped_morphisms = iter_grouped_morphisms(rule, eqlog);
    let first_morphism = match grouped_morphisms.next() {
        None => {
            let sorts = BTreeMap::new();
            let sequent = FlatSequent {
                premise: Vec::new(),
                conclusion: Vec::new(),
            };
            return SequentFlattening {
                name,
                sequent,
                sorts,
            };
        }
        Some(m) => m,
    };

    if eqlog.if_morphism(first_morphism) {
        premise = flatten_delta(first_morphism, &mut flat_names, eqlog, identifiers);
        premise_flat_terms = flat_names.values().flatten().copied().collect();
    } else {
        assert!(
            eqlog.surj_then_morphism(first_morphism)
                || eqlog.non_surj_then_morphism(first_morphism),
            "Every grouped morphism should be if, surj_then or non_surj_then"
        );
        conclusion.extend(flatten_delta(
            first_morphism,
            &mut flat_names,
            eqlog,
            identifiers,
        ));
    }

    for morph in grouped_morphisms {
        assert!(
            eqlog.surj_then_morphism(morph) || eqlog.non_surj_then_morphism(morph),
            "Every morphism after the first must be a then morphism"
        );
        conclusion.extend(flatten_delta(morph, &mut flat_names, eqlog, identifiers));
    }

    let conclusion = sort_then_atoms(conclusion, premise_flat_terms, eqlog, identifiers);
    let sorts = sort_map(&flat_names, eqlog, identifiers);
    let sequent = FlatSequent {
        premise,
        conclusion,
    };

    #[cfg(debug_assertions)]
    sequent.check();

    SequentFlattening {
        name,
        sequent,
        sorts,
    }
}
