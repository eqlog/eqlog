use std::collections::BTreeMap;

use crate::flat_ast::*;
use crate::flatten::SequentFlattening;
use eqlog_eqlog::*;

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

    result.reverse();
    result
}

pub fn get_flat_term_or_create(el: El, flat_names: &mut BTreeMap<El, FlatTerm>) -> FlatTerm {
    let len = flat_names.len();
    *flat_names.entry(el).or_insert(FlatTerm(len))
}

pub fn flatten_delta(
    morphism: Morphism,
    flat_names: BTreeMap<El, FlatTerm>,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<String, Ident>,
) -> (BTreeMap<El, FlatTerm>, Vec<FlatAtom>) {
    let codomain = eqlog.cod(morphism).unwrap();
    let mut atoms: Vec<FlatAtom> = Vec::new();

    for (el0, el1) in iter_in_ker(morphism, eqlog) {
        if !eqlog.are_equal_el(el0, el1) {
            let tm0 = *flat_names
                .get(&el0)
                .expect("domain els must already have names");
            let tm1 = *flat_names
                .get(&el1)
                .expect("domain els must already have names");
            atoms.push(FlatAtom::Equal(tm0, tm1));
        }
    }

    let mut flat_names: BTreeMap<_, _> = flat_names
        .into_iter()
        .map(|(el, flat_term)| (eqlog.map_el(morphism, el).unwrap(), flat_term))
        .collect();

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
    flat_names: &BTreeMap<El, FlatTerm>,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<String, Ident>,
) -> BTreeMap<FlatTerm, String> {
    flat_names
        .iter()
        .map(|(el, tm)| {
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

            (*tm, type_name.to_string())
        })
        .collect()
}

pub fn flatten(
    rule: RuleDeclNode,
    eqlog: &mut Eqlog,
    identifiers: &BTreeMap<String, Ident>,
) -> SequentFlattening {
    let chain = eqlog.rule_chain(rule).unwrap();
    let restricted_chain = RestrictedChain::from_chain(chain, eqlog);

    match restricted_chain {
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
            let (flat_names, conclusion) =
                flatten_delta(initiality_morphism, BTreeMap::new(), eqlog, identifiers);
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
            let (flat_names, conclusion) = flatten_delta(morphism, flat_names, eqlog, identifiers);
            let sequent = FlatSequent {
                premise,
                conclusion,
            };
            let sorts = sort_map(&flat_names, eqlog, identifiers);
            SequentFlattening { sequent, sorts }
        }
    }
}
