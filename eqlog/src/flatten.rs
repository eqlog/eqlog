use std::collections::{BTreeMap, BTreeSet};

use crate::flat_ast::*;
use eqlog_eqlog::*;
use maplit::btreeset;

pub struct SequentFlattening {
    pub sequent: FlatSequent,
    pub sorts: BTreeMap<FlatTerm, String>,
}

/// A chain with at most one morphism (i.e. two objects).
///
/// This is useful for the time being since general chains are not supported yet.
enum RestrictedChain {
    Empty {
        #[allow(unused)]
        chain: Chain,
    },
    Singleton {
        #[allow(unused)]
        chain: Chain,
        structure: Structure,
    },
    Morphism {
        #[allow(unused)]
        chain: Chain,
        domain: Structure,
        morphism: Morphism,
        #[allow(unused)]
        codomain: Structure,
    },
}

impl RestrictedChain {
    fn from_chain(chain: Chain, eqlog: &Eqlog) -> Self {
        if eqlog
            .iter_nil_chain()
            .find(|ch| eqlog.are_equal_chain(*ch, chain))
            .is_some()
        {
            return RestrictedChain::Empty { chain };
        }

        let tail = eqlog.chain_tail(chain).unwrap();
        let structure = eqlog.chain_head_structure(chain).unwrap();

        if eqlog
            .iter_nil_chain()
            .find(|ch| eqlog.are_equal_chain(*ch, tail))
            .is_some()
        {
            return RestrictedChain::Singleton { chain, structure };
        }

        let domain = structure;
        let morphism = eqlog.chain_head_transition(chain).unwrap();
        let codomain = eqlog.chain_head_structure(tail).unwrap();

        RestrictedChain::Morphism {
            chain,
            domain,
            morphism,
            codomain,
        }
    }
}

pub fn iter_els<'a>(structure: Structure, eqlog: &'a Eqlog) -> impl 'a + Iterator<Item = El> {
    eqlog.iter_el_structure().filter_map(move |(el, strct)| {
        if eqlog.are_equal_structure(strct, structure) {
            Some(el)
        } else {
            None
        }
    })
}

pub fn iter_pred_app<'a>(
    structure: Structure,
    eqlog: &'a Eqlog,
) -> impl 'a + Iterator<Item = (Pred, ElList)> {
    eqlog.iter_pred_app().filter_map(move |(pred, args)| {
        if !eqlog.are_equal_structure(eqlog.els_structure(args).unwrap(), structure) {
            return None;
        }

        Some((pred, args))
    })
}

pub fn iter_func_app<'a>(
    structure: Structure,
    eqlog: &'a Eqlog,
) -> impl 'a + Iterator<Item = (Func, ElList, El)> {
    eqlog
        .iter_func_app()
        .filter_map(move |(func, args, result)| {
            if !eqlog.are_equal_structure(eqlog.els_structure(args).unwrap(), structure) {
                return None;
            }
            assert!(eqlog.are_equal_structure(eqlog.el_structure(result).unwrap(), structure));

            Some((func, args, result))
        })
}

pub fn iter_in_ker<'a>(
    morphism: Morphism,
    eqlog: &'a Eqlog,
) -> impl 'a + Iterator<Item = (El, El)> {
    eqlog.iter_in_ker().filter_map(move |(morph, el0, el1)| {
        if !eqlog.are_equal_morphism(morphism, morph) {
            return None;
        }

        Some((el0, el1))
    })
}

pub fn el_list_vec(mut els: ElList, eqlog: &Eqlog) -> Vec<El> {
    let mut result = Vec::new();
    loop {
        let cons_entry = eqlog
            .iter_cons_el_list()
            .find(|(_, _, cons_els)| eqlog.are_equal_el_list(*cons_els, els));
        if let Some((head_el, tail_els, _)) = cons_entry {
            result.push(head_el);
            els = tail_els;
            continue;
        }

        assert!(eqlog
            .iter_nil_el_list()
            .find(|(_, nil)| eqlog.are_equal_el_list(els, *nil))
            .is_some());
        break;
    }

    result
}

pub fn get_flat_term_or_create(
    el: El,
    flat_names: &mut BTreeMap<El, BTreeSet<FlatTerm>>,
) -> FlatTerm {
    let len = flat_names
        .iter()
        .map(|(_, flat_terms)| flat_terms.len())
        .sum();
    let names = flat_names.entry(el).or_insert(btreeset! {FlatTerm(len)});
    *names.iter().next().unwrap()
}

pub fn flatten_delta(
    morphism: Morphism,
    mut flat_names: BTreeMap<El, BTreeSet<FlatTerm>>,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<String, Ident>,
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
            let pred_name = identifiers
                .iter()
                .find_map(|(name, ident)| {
                    eqlog
                        .are_equal_ident(*ident, pred_ident)
                        .then_some(name.as_str())
                })
                .unwrap();
            atoms.push(FlatAtom::Relation(pred_name.to_string(), el_terms));
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
            let func_name = identifiers
                .iter()
                .find_map(|(name, ident)| {
                    eqlog
                        .are_equal_ident(*ident, func_ident)
                        .then_some(name.as_str())
                })
                .unwrap();
            atoms.push(FlatAtom::Relation(func_name.to_string(), tuple));
        }
    }

    for el in iter_els(codomain, eqlog) {
        if !eqlog.el_in_img(morphism, el) && !eqlog.constrained_el(el) {
            let tm = get_flat_term_or_create(el, &mut flat_names);

            let typ = eqlog.el_type(el).unwrap();
            let type_ident = eqlog
                .iter_semantic_type()
                .find_map(|(ident, tp)| eqlog.are_equal_type(tp, typ).then_some(ident))
                .unwrap();
            let type_name = identifiers
                .iter()
                .find_map(|(name, ident)| {
                    eqlog
                        .are_equal_ident(*ident, type_ident)
                        .then_some(name.as_str())
                })
                .unwrap();
            atoms.push(FlatAtom::Unconstrained(tm, type_name.to_string()));
        }
    }

    (flat_names, atoms)
}

pub fn sort_map(
    flat_names: &BTreeMap<El, BTreeSet<FlatTerm>>,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<String, Ident>,
) -> BTreeMap<FlatTerm, String> {
    flat_names
        .iter()
        .map(|(el, tms)| {
            let typ = eqlog.el_type(*el).unwrap();
            let type_ident = eqlog
                .iter_semantic_type()
                .find_map(|(ident, tp)| eqlog.are_equal_type(tp, typ).then_some(ident))
                .unwrap();
            let type_name = identifiers
                .iter()
                .find_map(|(name, ident)| {
                    eqlog
                        .are_equal_ident(*ident, type_ident)
                        .then_some(name.as_str())
                })
                .unwrap();

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
pub fn sort_then_atoms(
    mut atoms: Vec<FlatAtom>,
    premise_flat_terms: BTreeSet<FlatTerm>,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<String, Ident>,
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
                        let rel_ident = identifiers.get(rel).unwrap();
                        let is_func = eqlog.semantic_func(*rel_ident).is_some();
                        let is_pred = eqlog.semantic_pred(*rel_ident).is_some();
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
    eqlog: &mut Eqlog,
    identifiers: &BTreeMap<String, Ident>,
) -> SequentFlattening {
    let chain = eqlog.rule_chain(rule).unwrap();
    let restricted_chain = RestrictedChain::from_chain(chain, eqlog);

    let flattening = match restricted_chain {
        RestrictedChain::Empty { chain: _ } => {
            let sequent = FlatSequent {
                premise: Vec::new(),
                conclusion: Vec::new(),
            };
            let sorts = BTreeMap::new();
            SequentFlattening { sequent, sorts }
        }
        RestrictedChain::Singleton {
            chain: _,
            structure,
        } => {
            let premise: Vec<FlatAtom> = Vec::new();
            let initiality_morphism = eqlog.initiality_morphism(structure).unwrap();
            let (flat_names, mut conclusion) =
                flatten_delta(initiality_morphism, BTreeMap::new(), eqlog, identifiers);
            let premise_terms = BTreeSet::new();
            conclusion = sort_then_atoms(conclusion, premise_terms, eqlog, identifiers);
            let sequent = FlatSequent {
                premise,
                conclusion,
            };
            let sorts = sort_map(&flat_names, eqlog, identifiers);
            SequentFlattening { sequent, sorts }
        }
        RestrictedChain::Morphism {
            chain: _,
            domain,
            morphism,
            codomain: _,
        } => {
            let initiality_morphism = eqlog.initiality_morphism(domain).unwrap();
            let (flat_names, premise) =
                flatten_delta(initiality_morphism, BTreeMap::new(), eqlog, identifiers);
            let premise_terms: BTreeSet<FlatTerm> =
                flat_names.values().flatten().copied().collect();
            let (flat_names, mut conclusion) =
                flatten_delta(morphism, flat_names, eqlog, identifiers);
            conclusion = sort_then_atoms(conclusion, premise_terms, eqlog, identifiers);
            let sequent = FlatSequent {
                premise,
                conclusion,
            };
            let sorts = sort_map(&flat_names, eqlog, identifiers);
            SequentFlattening { sequent, sorts }
        }
    };

    #[cfg(debug_assertions)]
    flattening.sequent.check();
    flattening
}
