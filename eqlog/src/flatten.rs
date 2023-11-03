use crate::eqlog_util::*;
use crate::flat_ast::*;
use eqlog_eqlog::*;
use maplit::btreeset;
use std::collections::{BTreeMap, BTreeSet};

pub struct SequentFlattening {
    pub name: Option<String>,
    pub sequent: FlatSequent,
    pub sorts: BTreeMap<FlatTerm, String>,
}

/// A chain with at most one morphism (i.e. two objects).
///
/// This is useful for the time being since general chains are not supported yet.
enum RestrictedChain {
    // The chain is given by just the initial structure, representing the empty rule.
    Initial(),
    // The chain is given by just then-transition from the initial structure, representing a rule
    // without if statements.
    OnlyThen {
        then_transition: Morphism,
    },
    // The chain is given by an "if" transition from the initial structure, followed by a "then"
    // transition. This represents a rule with if statements followed by then statements.
    IfThen {
        if_transition: Morphism,
        then_transition: Morphism,
    },
}

impl RestrictedChain {
    fn from_grouped_rule_chain(chain: Chain, eqlog: &Eqlog) -> Self {
        let tail = eqlog
            .chain_tail(chain)
            .expect("Grouped rule chains should not be empty");
        let first_struct = eqlog
            .chain_head_structure(chain)
            .expect("Grouped rule chains should not be empty");
        assert!(
            eqlog.are_equal_structure(first_struct, eqlog.initial_structure().unwrap()),
            "Grouped rule chains should always start with the initial structure"
        );

        if eqlog.are_equal_chain(tail, eqlog.nil_chain().unwrap()) {
            return RestrictedChain::Initial();
        }

        let first_second_trans = eqlog
            .chain_head_transition(chain)
            .expect("Chains with non-nil tail should have a head transition");
        let tail_tail = eqlog
            .chain_tail(tail)
            .expect("Non-nil chain should have a tail");
        if eqlog.are_equal_chain(tail_tail, eqlog.nil_chain().unwrap()) {
            return RestrictedChain::OnlyThen {
                then_transition: first_second_trans,
            };
        }

        let second_third_trans = eqlog
            .chain_head_transition(tail)
            .expect("Chains with non-nil tail should have a head transition");
        let tail_tail_tail = eqlog
            .chain_tail(tail_tail)
            .expect("Chains with non-nil tail should have a head transition");
        assert!(
            eqlog.are_equal_chain(tail_tail_tail, eqlog.nil_chain().unwrap()),
            "Grouped rule chains should not have more than 3 structures"
        );

        RestrictedChain::IfThen {
            if_transition: first_second_trans,
            then_transition: second_third_trans,
        }
    }
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
    mut flat_names: BTreeMap<El, BTreeSet<FlatTerm>>,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> (BTreeMap<El, BTreeSet<FlatTerm>>, Vec<FlatAtom>) {
    let codomain = eqlog.cod(morphism).unwrap();
    let mut atoms: Vec<FlatAtom> = Vec::new();

    for (el0, el1) in iter_in_ker(morphism, eqlog) {
        if !eqlog.are_equal_el(el0, el1) {
            let tm0 = get_flat_term_or_create(el0, &mut flat_names);
            let tm1 = get_flat_term_or_create(el1, &mut flat_names);
            atoms.push(FlatAtom::Equal(tm0, tm1));
        }
    }

    flat_names = {
        let mut new_flat_names = BTreeMap::new();
        for (el, tms) in flat_names.into_iter() {
            let img_el = eqlog.map_el(morphism, el).unwrap();
            for tm in tms {
                new_flat_names
                    .entry(img_el)
                    .or_insert(BTreeSet::new())
                    .insert(tm);
            }
        }
        new_flat_names
    };

    for (pred, els) in iter_pred_app(codomain, eqlog) {
        if !eqlog.pred_tuple_in_img(morphism, pred, els) {
            let el_terms: Vec<FlatTerm> = el_list_vec(els, eqlog)
                .into_iter()
                .map(|el| get_flat_term_or_create(el, &mut flat_names))
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
                .map(|el| get_flat_term_or_create(el, &mut flat_names))
                .collect();
            let result_term = get_flat_term_or_create(result, &mut flat_names);

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
            let tm = get_flat_term_or_create(el, &mut flat_names);

            let typ = el_type(el, eqlog).unwrap();
            let type_ident = eqlog
                .iter_semantic_type()
                .find_map(|(ident, tp)| eqlog.are_equal_type(tp, typ).then_some(ident))
                .unwrap();
            let type_name: String = identifiers.get(&type_ident).unwrap().to_string();
            atoms.push(FlatAtom::Unconstrained(tm, type_name));
        }
    }

    (flat_names, atoms)
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
    let chain = eqlog.grouped_rule_chain(rule).unwrap();
    let restricted_chain = RestrictedChain::from_grouped_rule_chain(chain, eqlog);
    let name = eqlog
        .rule_name(rule)
        .map(|ident| identifiers.get(&ident).unwrap().to_string());

    let flattening = match restricted_chain {
        RestrictedChain::Initial() => {
            let sequent = FlatSequent {
                premise: Vec::new(),
                conclusion: Vec::new(),
            };
            let sorts = BTreeMap::new();
            SequentFlattening {
                name,
                sequent,
                sorts,
            }
        }
        RestrictedChain::OnlyThen { then_transition } => {
            let premise = Vec::new();
            let flat_names = BTreeMap::new();
            let premise_terms: BTreeSet<FlatTerm> = BTreeSet::new();

            let (flat_names, mut conclusion) =
                flatten_delta(then_transition, flat_names, eqlog, identifiers);
            conclusion = sort_then_atoms(conclusion, premise_terms, eqlog, identifiers);

            let sequent = FlatSequent {
                premise,
                conclusion,
            };
            let sorts = sort_map(&flat_names, eqlog, identifiers);
            SequentFlattening {
                name,
                sequent,
                sorts,
            }
        }
        RestrictedChain::IfThen {
            if_transition,
            then_transition,
        } => {
            let flat_names = BTreeMap::new();
            let (flat_names, premise) =
                flatten_delta(if_transition, flat_names, eqlog, identifiers);
            let premise_terms: BTreeSet<FlatTerm> =
                flat_names.values().flatten().copied().collect();

            let (flat_names, mut conclusion) =
                flatten_delta(then_transition, flat_names, eqlog, identifiers);
            conclusion = sort_then_atoms(conclusion, premise_terms, eqlog, identifiers);

            let sequent = FlatSequent {
                premise,
                conclusion,
            };
            let sorts = sort_map(&flat_names, eqlog, identifiers);
            SequentFlattening {
                name,
                sequent,
                sorts,
            }
        } // RestrictedChain::Morphism {
          //     chain: _,
          //     domain,
          //     morphism,
          //     codomain: _,
          // } => {
          //     let initiality_morphism = eqlog.initiality_morphism(domain).unwrap();
          //     let (flat_names, premise) =
          //         flatten_delta(initiality_morphism, BTreeMap::new(), eqlog, identifiers);
          //     let premise_terms: BTreeSet<FlatTerm> =
          //         flat_names.values().flatten().copied().collect();
          //     let (flat_names, mut conclusion) =
          //         flatten_delta(morphism, flat_names, eqlog, identifiers);
          //     conclusion = sort_then_atoms(conclusion, premise_terms, eqlog, identifiers);
          //     let sequent = FlatSequent {
          //         premise,
          //         conclusion,
          //     };
          //     let sorts = sort_map(&flat_names, eqlog, identifiers);
          //     SequentFlattening {
          //         name,
          //         sequent,
          //         sorts,
          //     }
          // }
    };

    #[cfg(debug_assertions)]
    flattening.sequent.check();
    flattening
}
