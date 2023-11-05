use crate::eqlog_util::*;
use crate::flat_ast::*;
use eqlog_eqlog::*;
use std::collections::BTreeMap;
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

/// Assign compatible [FlatTerm]s to the [El]s of in a chain of morphisms. The first morphism must
/// have empty domain.
///
/// The assigne [FlatTerm]s are compatible with morphisms in the sense that if f : X -> Y is a
/// morphism in the chain and y is in the range of f, then the [FlatTerm] assigned to y is one of
/// the [FlatTerm]s assigned to a preimage of y.
fn assign_el_terms(
    chain: impl IntoIterator<Item = Morphism>,
    eqlog: &Eqlog,
) -> BTreeMap<El, FlatTerm> {
    let mut el_terms = BTreeMap::new();
    let mut unused_flat_terms = (0..).into_iter().map(FlatTerm);

    let mut is_first = true;
    for transition in chain {
        if is_first {
            let dom = eqlog.dom(transition).expect("dom should be total");
            assert!(
                iter_els(dom, eqlog).next().is_none(),
                "the first domain should be empty"
            );
            is_first = false;
        }

        for (m, preimage, image) in eqlog.iter_map_el() {
            if !eqlog.are_equal_morphism(m, transition) {
                continue;
            }

            if let Some(tm) = el_terms.get(&preimage) {
                el_terms.insert(image, *tm);
            }
        }

        let cod = eqlog.cod(transition).expect("cod should be total");
        for el in iter_els(cod, eqlog) {
            el_terms
                .entry(el)
                .or_insert_with(|| unused_flat_terms.next().unwrap());
        }
    }

    el_terms
}

fn flatten_delta(
    morphism: Morphism,
    flat_terms: &BTreeMap<El, FlatTerm>,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> Vec<FlatAtom> {
    let codomain = eqlog.cod(morphism).unwrap();
    let mut atoms: Vec<FlatAtom> = Vec::new();

    for (el0, el1) in iter_in_ker(morphism, eqlog) {
        if !eqlog.are_equal_el(el0, el1) {
            let tm0 = *flat_terms.get(&el0).unwrap();
            let tm1 = *flat_terms.get(&el1).unwrap();
            atoms.push(FlatAtom::Equal(tm0, tm1));
        }
    }

    for (pred, els) in iter_pred_app(codomain, eqlog) {
        if !eqlog.pred_tuple_in_img(morphism, pred, els) {
            let el_terms: Vec<FlatTerm> = el_list_vec(els, eqlog)
                .into_iter()
                .map(|el| *flat_terms.get(&el).unwrap())
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
                .map(|el| *flat_terms.get(&el).unwrap())
                .collect();
            let result_term = *flat_terms.get(&result).unwrap();

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
            let tm = *flat_terms.get(&el).unwrap();

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
    flat_names: &BTreeMap<El, FlatTerm>,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> BTreeMap<FlatTerm, String> {
    flat_names
        .iter()
        .map(|(el, tm)| {
            let typ = el_type(*el, eqlog).unwrap();
            let type_ident = eqlog
                .iter_semantic_type()
                .find_map(|(ident, tp)| eqlog.are_equal_type(tp, typ).then_some(ident))
                .unwrap();
            let type_name = identifiers.get(&type_ident).unwrap().to_string();

            (*tm, type_name)
        })
        .collect()
}

pub fn flatten(
    rule: RuleDeclNode,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> SequentFlattening {
    let name = eqlog
        .rule_name(rule)
        .map(|ident| identifiers.get(&ident).unwrap().to_string());
    let mut premise = Vec::new();
    let mut conclusion = Vec::new();
    let flat_terms = assign_el_terms(iter_grouped_morphisms(rule, eqlog), eqlog);

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
        premise = flatten_delta(first_morphism, &flat_terms, eqlog, identifiers);
    } else {
        assert!(
            eqlog.surj_then_morphism(first_morphism)
                || eqlog.non_surj_then_morphism(first_morphism),
            "Every grouped morphism should be if, surj_then or non_surj_then"
        );
        conclusion.extend(flatten_delta(
            first_morphism,
            &flat_terms,
            eqlog,
            identifiers,
        ));
    }

    for morph in grouped_morphisms {
        assert!(
            eqlog.surj_then_morphism(morph) || eqlog.non_surj_then_morphism(morph),
            "Every morphism after the first must be a then morphism"
        );
        conclusion.extend(flatten_delta(morph, &flat_terms, eqlog, identifiers));
    }

    let sorts = sort_map(&flat_terms, eqlog, identifiers);
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
