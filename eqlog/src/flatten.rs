use crate::eqlog_util::*;
use crate::flat_eqlog::*;
use eqlog_eqlog::*;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::sync::Arc;

/// Assign compatible [FlatTerm]s to the [El]s in the codomains of a list of morphisms.
///
/// The function takes the list of morphisms as an iterator over [Morphism] elements. These
/// morphisms must be such that no two morphisms have the same codomain.
///
/// The assigned [FlatTerm]s are compatible with morphisms in the sense that if f : X -> Y is one
/// of the provided morphisms and y is in the range of f, then the [FlatTerm] assigned to y is one
/// of the [FlatTerm]s assigned to a preimage of y.
fn assign_el_vars(
    morphisms: impl IntoIterator<Item = Morphism>,
    eqlog: &Eqlog,
) -> BTreeMap<El, FlatVar> {
    let mut el_vars: BTreeMap<El, FlatVar> = BTreeMap::new();
    let mut available_vars = 0..;

    for transition in morphisms {
        for (m, preimage, image) in eqlog.iter_map_el() {
            if !eqlog.are_equal_morphism(m, transition) {
                continue;
            }

            if let Some(var) = el_vars.get(&preimage) {
                el_vars.insert(image, var.clone());
            }
        }

        let cod = eqlog.cod(transition).expect("cod should be total");
        for el in iter_els(cod, eqlog) {
            el_vars.entry(el).or_insert_with(|| {
                let typ = match eqlog.element_type_case(el_type(el, eqlog).unwrap()) {
                    ElementTypeCase::AmbientType(typ) => typ,
                    ElementTypeCase::InstantiatedType(_, typ) => typ,
                };
                let name: Arc<str> = format!("el{}", available_vars.next().unwrap()).into();
                FlatVar { name, typ }
            });
        }
    }

    el_vars
}

fn iter_rel_app<'a>(
    strct: Structure,
    eqlog: &'a Eqlog,
) -> impl 'a + Iterator<Item = (Rel, ElList)> {
    eqlog.iter_rel_app().filter_map(move |(rel, els)| {
        if eqlog.are_equal_structure(eqlog.els_structure(els).unwrap(), strct) {
            Some((rel, els))
        } else {
            None
        }
    })
}

/// Returns a list of if statements which match the delta given by `morphism` with arbitrary (not
/// necessarily fresh) data.
///
/// The output statements assumes that data in the domain of the morphism has already been matched.
fn flatten_if_arbitrary(
    morphism: Morphism,
    el_vars: &BTreeMap<El, FlatVar>,
    eqlog: &Eqlog,
) -> Vec<FlatIfStmt> {
    let mut stmts = Vec::new();

    for (el0, el1) in iter_in_ker(morphism, eqlog) {
        if !eqlog.are_equal_el(el0, el1) {
            let lhs = el_vars.get(&el0).unwrap().clone();
            let rhs = el_vars.get(&el1).unwrap().clone();
            assert_eq!(lhs.typ, rhs.typ);
            let rel = FlatInRel::Equality(lhs.typ);
            stmts.push(FlatIfStmt {
                rel,
                args: vec![lhs, rhs],
                age: QueryAge::All,
            });
        }
    }

    let cod = eqlog.cod(morphism).expect("cod should be total");

    for (rel, els) in iter_rel_app(cod, eqlog) {
        if eqlog.rel_tuple_in_img(morphism, rel, els) {
            continue;
        }

        let model_el: Option<El> = eqlog.rel_app_parent_model_el(rel, els);
        let els_vec: Vec<El> = el_list_vec(els, eqlog);
        let args: Vec<FlatVar> = model_el
            .into_iter()
            .chain(els_vec)
            .map(|el| el_vars.get(&el).unwrap().clone())
            .collect();

        let age = QueryAge::All;
        let rel = FlatInRel::EqlogRel(rel);
        stmts.push(FlatIfStmt { rel, args, age });
    }

    for el in iter_els(cod, eqlog)
        .filter(move |&el| !eqlog.el_in_img(morphism, el) && !eqlog.constrained_el(el))
    {
        let var = el_vars.get(&el).unwrap().clone();
        let age = QueryAge::All;
        let el_typ = el_type(el, eqlog).unwrap();

        let (parent_var, typ) = match eqlog.element_type_case(el_typ) {
            ElementTypeCase::AmbientType(typ) => {
                let typ_def_sym_scope = eqlog.type_definition_symbol_scope(typ).unwrap();
                let el_struct = eqlog.el_structure(el).unwrap();
                let model_var = eqlog
                    .ambient_model_el(typ_def_sym_scope, el_struct)
                    .map(|model_el| el_vars.get(&model_el).unwrap().clone());
                (model_var, typ)
            }
            ElementTypeCase::InstantiatedType(model_el, typ) => {
                let var = Some(el_vars.get(&model_el).unwrap().clone());
                (var, typ)
            }
        };

        let if_stmt = match parent_var {
            None => {
                let rel = FlatInRel::TypeSet(typ);
                FlatIfStmt {
                    rel,
                    args: vec![var],
                    age,
                }
            }
            Some(parent_var) => {
                let rel: Rel = eqlog
                    .func_rel(eqlog.parent_model_func(typ).unwrap())
                    .unwrap();
                let rel = FlatInRel::EqlogRel(rel);
                FlatIfStmt {
                    rel,
                    args: vec![var, parent_var],
                    age,
                }
            }
        };
        stmts.push(if_stmt);
    }

    stmts
}

/// Emits a then block corresponding to the lift against a `morphism`.
///
/// The provided `morphism` must be surjective.
fn flatten_surj_then(
    morphism: Morphism,
    el_vars: &BTreeMap<El, FlatVar>,
    eqlog: &Eqlog,
) -> Vec<FlatThenStmt> {
    let mut stmts = Vec::new();

    for (el0, el1) in iter_in_ker(morphism, eqlog) {
        if !eqlog.are_equal_el(el0, el1) {
            let lhs = el_vars.get(&el0).unwrap().clone();
            let rhs = el_vars.get(&el1).unwrap().clone();

            assert_eq!(lhs.typ, rhs.typ);
            let rel = FlatOutRel::Equality(lhs.typ);
            stmts.push(FlatThenStmt {
                rel,
                args: vec![lhs, rhs],
            });
        }
    }

    let cod = eqlog.cod(morphism).expect("cod should be total");

    for (rel, els) in iter_rel_app(cod, eqlog) {
        if eqlog.rel_tuple_in_img(morphism, rel, els) {
            continue;
        }

        let model_el: Option<El> = eqlog.rel_app_parent_model_el(rel, els);
        let els_vec: Vec<El> = el_list_vec(els, eqlog);
        let args: Vec<FlatVar> = model_el
            .into_iter()
            .chain(els_vec)
            .map(|el| el_vars.get(&el).unwrap().clone())
            .collect();

        let rel = FlatOutRel::EqlogRel(rel);
        stmts.push(FlatThenStmt { rel, args });
    }

    assert!(
        !iter_els(cod, eqlog)
            .find(|el| !eqlog.el_in_img(morphism, *el))
            .is_some(),
        "morphism should be surjective"
    );

    stmts
}

/// Emits a non-surjective then statement corresponding to a lift against the provided `morphism`
/// if necessary.
///
/// The provided `morphism` must be given by at most a a single new term (or the identity), i.e. a
/// pushout along making a function defined on a single argument tuple.
fn flatten_non_surj_then(
    morphism: Morphism,
    el_vars: &BTreeMap<El, FlatVar>,
    eqlog: &Eqlog,
) -> Option<(FlatIfStmt, FlatThenStmt)> {
    let cod = eqlog.cod(morphism).expect("cod should be total");
    let cod_els: BTreeSet<El> = iter_els(cod, eqlog).collect();
    let img_els: BTreeSet<El> = eqlog
        .iter_map_el()
        .filter_map(|(morphism0, _, image)| {
            if eqlog.are_equal_morphism(morphism0, morphism) {
                Some(image)
            } else {
                None
            }
        })
        .collect();

    let mut new_els = cod_els.difference(&img_els).copied();
    let new_el: Option<El> = new_els.next();
    assert!(
        new_els.next().is_none(),
        "There should be at most one new element in the codomain"
    );

    let new_el = match new_el {
        Some(new_el) => new_el,
        None => {
            return None;
        }
    };

    let (func, func_arg_els) = eqlog
        .iter_func_app()
        .find_map(|(func, args, result)| {
            if eqlog.are_equal_el(result, new_el) {
                Some((func, args))
            } else {
                None
            }
        })
        .expect("new element should be the result of func_app");
    let func_arg_els_vec = el_list_vec(func_arg_els, eqlog);
    assert!(
        func_arg_els_vec
            .iter()
            .copied()
            .all(|arg| img_els.contains(&arg)),
        "Arguments to obtain new element should be in image"
    );

    let rel = eqlog.func_rel(func).unwrap();
    let rel_arg_els = eqlog.snoc_el_list(func_arg_els, new_el).unwrap();
    let model_el: Option<El> = eqlog.rel_app_parent_model_el(rel, rel_arg_els);

    let flat_func_args: Vec<FlatVar> = model_el
        .into_iter()
        .chain(func_arg_els_vec)
        .map(|el| el_vars.get(&el).unwrap().clone())
        .collect();

    let result_var = el_vars.get(&new_el).unwrap().clone();

    let then_stmt = FlatThenStmt {
        rel: FlatOutRel::FuncDomain(func),
        args: flat_func_args.clone(),
    };
    let if_stmt = FlatIfStmt {
        rel: FlatInRel::EqlogRel(rel),
        args: flat_func_args.into_iter().chain([result_var]).collect(),
        age: QueryAge::All,
    };

    Some((if_stmt, then_stmt))
}

/// Compiles an Eqlog [RuleDeclNode] into a set of [FlatRule]s.
fn flatten_rule(
    rule: RuleDeclNode,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> Vec<FlatRule> {
    let name = match eqlog.rule_name(rule) {
        Some(ident) => identifiers.get(&ident).unwrap().to_string(),
        None => format!("anonymous_rule_{}", rule.0),
    };

    let el_vars = assign_el_vars(iter_rule_morphisms(rule, eqlog).flatten(), eqlog);

    let mut rules: Vec<FlatRule> = Vec::new();
    let mut matching_stmts: BTreeMap<Structure, Vec<FlatIfStmt>> = BTreeMap::new();

    matching_stmts.insert(eqlog.before_rule_structure(rule).unwrap(), Vec::new());

    for morphism in iter_rule_morphisms(rule, eqlog).flatten() {
        let dom_matching_stmts: &[FlatIfStmt] = matching_stmts
            .get(&eqlog.dom(morphism).unwrap())
            .unwrap()
            .as_slice();

        let cod = eqlog.cod(morphism).expect("cod should be total");

        let cod_matching_stmts: Vec<FlatIfStmt> = if eqlog.if_morphism(morphism) {
            dom_matching_stmts
                .into_iter()
                .cloned()
                .chain(flatten_if_arbitrary(morphism, &el_vars, eqlog))
                .collect()
        } else if eqlog.surj_then_morphism(morphism) {
            let name = format!("{name}_{}", rules.len());
            let premise: Vec<FlatIfStmt> = dom_matching_stmts.to_vec();
            let conclusion = flatten_surj_then(morphism, &el_vars, eqlog);
            rules.push(FlatRule {
                name,
                premise,
                conclusion,
            });
            let cod_matching_stmts = dom_matching_stmts.to_vec();
            cod_matching_stmts
        } else if eqlog.non_surj_then_morphism(morphism) {
            let name = format!("{name}_{}", rules.len());
            let premise: Vec<FlatIfStmt> = dom_matching_stmts.to_vec();
            let mut cod_matching_stmts = dom_matching_stmts.to_vec();
            if let Some(stmts) = flatten_non_surj_then(morphism, &el_vars, eqlog) {
                let (if_stmt, then_stmt) = stmts;
                rules.push(FlatRule {
                    name,
                    premise,
                    conclusion: vec![then_stmt],
                });
                cod_matching_stmts.push(if_stmt);
            }
            cod_matching_stmts
        } else if eqlog.noop_morphism(morphism) {
            let cod_matching_stmts = dom_matching_stmts.to_vec();
            cod_matching_stmts
        } else {
            panic!("Every rule morphism must be either if, surj_then or non_surj_then");
        };

        let prev_cod_matching_stmts = matching_stmts.insert(cod, cod_matching_stmts);
        assert!(prev_cod_matching_stmts.is_none());
    }

    rules
}

pub fn flatten(eqlog: &Eqlog, identifiers: &BTreeMap<Ident, String>) -> Vec<FlatRule> {
    let mut rules_vec: Vec<FlatRule> = Vec::new();

    rules_vec.extend(
        eqlog
            .iter_func()
            .map(|func| semi_naive_functionality(func, &eqlog)),
    );
    rules_vec.extend(
        eqlog
            .iter_rule_decl_node()
            .flat_map(|rule| flatten_rule(rule, &eqlog, &identifiers))
            .flat_map(|flat_rule| to_semi_naive(&eliminate_equalities_ifs(&flat_rule))),
    );

    for rule in rules_vec.iter_mut() {
        sort_premise(rule);
    }

    rules_vec
}
