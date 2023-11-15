use crate::eqlog_util::*;
use crate::flat_eqlog::*;
use eqlog_eqlog::*;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::iter::successors;

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
fn assign_el_vars(
    chain: impl IntoIterator<Item = Morphism>,
    eqlog: &Eqlog,
) -> BTreeMap<El, FlatVar> {
    let mut el_terms = BTreeMap::new();
    let mut unused_flat_terms = (0..).into_iter().map(FlatVar);

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

fn make_var_type_map(el_vars: &BTreeMap<El, FlatVar>, eqlog: &Eqlog) -> BTreeMap<FlatVar, Type> {
    el_vars
        .iter()
        .map(|(el, var)| {
            let typ = el_type(*el, eqlog).unwrap();
            (*var, typ)
        })
        .collect()
}

/// Emits an if block which matches the delta given by `morphism` with arbitrary (not necessarily
/// fresh) data.
///
/// The output block assumes that data in the domain of the morphism has already been matched.
fn flatten_if_arbitrary(
    morphism: Morphism,
    el_vars: &BTreeMap<El, FlatVar>,
    eqlog: &Eqlog,
) -> Vec<FlatStmt> {
    let mut stmts = Vec::new();

    for (el0, el1) in iter_in_ker(morphism, eqlog) {
        if !eqlog.are_equal_el(el0, el1) {
            let lhs = *el_vars.get(&el0).unwrap();
            let rhs = *el_vars.get(&el1).unwrap();
            stmts.push(FlatStmt::If(FlatIfStmt::Equal(FlatStmtEqual { lhs, rhs })));
        }
    }

    let cod = eqlog.cod(morphism).expect("cod should be total");

    for (pred, els) in iter_pred_app(cod, eqlog) {
        if !eqlog.pred_tuple_in_img(morphism, pred, els) {
            let args: Vec<FlatVar> = el_list_vec(els, eqlog)
                .into_iter()
                .map(|el| *el_vars.get(&el).unwrap())
                .collect();
            let rel = Rel::Pred(pred);
            let only_dirty = false;
            stmts.push(FlatStmt::If(FlatIfStmt::Relation(FlatIfStmtRelation {
                rel,
                args,
                only_dirty,
            })));
        }
    }

    for (func, args, result) in iter_func_app(cod, eqlog) {
        if !eqlog.func_app_in_img(morphism, func, args) {
            let func_args: Vec<FlatVar> = el_list_vec(args, eqlog)
                .into_iter()
                .map(|el| *el_vars.get(&el).unwrap())
                .collect();
            let result = *el_vars.get(&result).unwrap();

            let args = {
                let mut a = func_args;
                a.push(result);
                a
            };

            let rel = Rel::Func(func);
            let only_dirty = false;
            stmts.push(FlatStmt::If(FlatIfStmt::Relation(FlatIfStmtRelation {
                rel,
                args,
                only_dirty,
            })));
        }
    }

    for el in iter_els(cod, eqlog) {
        if !eqlog.el_in_img(morphism, el) && !eqlog.constrained_el(el) {
            let var = *el_vars.get(&el).unwrap();
            let only_dirty = false;
            stmts.push(FlatStmt::If(FlatIfStmt::Type(FlatIfStmtType {
                var,
                only_dirty,
            })));
        }
    }

    stmts
}

/// Generates flat if blocks which together match the delta given by `morphism` with fresh data.
///
/// In contrast to [flatten_if_arbitrary], the output blocks assume that *no* data has been matched
/// so far.
fn flatten_if_fresh(
    morphism: Morphism,
    el_vars: &BTreeMap<El, FlatVar>,
    eqlog: &Eqlog,
) -> Vec<Vec<FlatStmt>> {
    let mut fresh_rel_tuples: Vec<(Rel, Vec<FlatVar>)> = Vec::new();
    let mut arbitrary_rel_tuples: Vec<(Rel, Vec<FlatVar>)> = Vec::new();

    let mut fresh_type_els: Vec<FlatVar> = Vec::new();
    let mut arbitrary_type_els: Vec<FlatVar> = Vec::new();

    let cod = eqlog.cod(morphism).expect("cod should be total");

    for (pred, els) in iter_pred_app(cod, eqlog) {
        let args: Vec<FlatVar> = el_list_vec(els, eqlog)
            .into_iter()
            .map(|el| *el_vars.get(&el).unwrap())
            .collect();
        let rel = Rel::Pred(pred);

        if eqlog.pred_tuple_in_img(morphism, pred, els) {
            arbitrary_rel_tuples.push((rel, args));
        } else {
            fresh_rel_tuples.push((rel, args));
        }
    }

    for (func, args, result) in iter_func_app(cod, eqlog) {
        let in_img = eqlog.func_app_in_img(morphism, func, args);
        let func_args: Vec<FlatVar> = el_list_vec(args, eqlog)
            .into_iter()
            .map(|el| *el_vars.get(&el).unwrap())
            .collect();
        let result = *el_vars.get(&result).unwrap();

        let args = {
            let mut a = func_args;
            a.push(result);
            a
        };
        let rel = Rel::Func(func);

        if in_img {
            arbitrary_rel_tuples.push((rel, args));
        } else {
            fresh_rel_tuples.push((rel, args));
        }
    }

    for el in iter_els(cod, eqlog).filter(|el| !eqlog.constrained_el(*el)) {
        let in_img = eqlog.el_in_img(morphism, el);
        let var = *el_vars.get(&el).unwrap();
        if in_img {
            arbitrary_type_els.push(var);
        } else {
            fresh_type_els.push(var);
        }
    }

    let mut blocks = Vec::new();

    for fresh_rel_index in 0..fresh_rel_tuples.len() {
        let mut block = Vec::new();

        for (i, (rel, args)) in fresh_rel_tuples
            .iter()
            .chain(arbitrary_rel_tuples.iter())
            .cloned()
            .enumerate()
        {
            let only_dirty = i == fresh_rel_index;
            block.push(FlatStmt::If(FlatIfStmt::Relation(FlatIfStmtRelation {
                rel,
                args,
                only_dirty,
            })));
        }

        for var in fresh_type_els
            .iter()
            .chain(arbitrary_type_els.iter())
            .copied()
        {
            let only_dirty = false;
            block.push(FlatStmt::If(FlatIfStmt::Type(FlatIfStmtType {
                var,
                only_dirty,
            })));
        }

        blocks.push(block);
    }

    for fresh_type_el_index in 0..fresh_type_els.len() {
        let mut block = Vec::new();

        for (rel, args) in fresh_rel_tuples
            .iter()
            .chain(arbitrary_rel_tuples.iter())
            .cloned()
        {
            let only_dirty = false;
            block.push(FlatStmt::If(FlatIfStmt::Relation(FlatIfStmtRelation {
                rel,
                args,
                only_dirty,
            })));
        }

        for (i, var) in fresh_type_els
            .iter()
            .chain(arbitrary_type_els.iter())
            .copied()
            .enumerate()
        {
            let only_dirty = i == fresh_type_el_index;
            block.push(FlatStmt::If(FlatIfStmt::Type(FlatIfStmtType {
                var,
                only_dirty,
            })));
        }

        blocks.push(block);
    }

    blocks
}

/// Emits a then block corresponding to the lift against a `morphism`.
///
/// The provided `morphism` must be surjective.
fn flatten_surj_then(
    morphism: Morphism,
    el_vars: &BTreeMap<El, FlatVar>,
    eqlog: &Eqlog,
) -> Vec<FlatStmt> {
    let mut stmts = Vec::new();

    for (el0, el1) in iter_in_ker(morphism, eqlog) {
        if !eqlog.are_equal_el(el0, el1) {
            let lhs = *el_vars.get(&el0).unwrap();
            let rhs = *el_vars.get(&el1).unwrap();
            stmts.push(FlatStmt::SurjThen(FlatSurjThenStmt::Equal(FlatStmtEqual {
                lhs,
                rhs,
            })));
        }
    }

    let cod = eqlog.cod(morphism).expect("cod should be total");

    for (pred, els) in iter_pred_app(cod, eqlog) {
        if !eqlog.pred_tuple_in_img(morphism, pred, els) {
            let args: Vec<FlatVar> = el_list_vec(els, eqlog)
                .into_iter()
                .map(|el| *el_vars.get(&el).unwrap())
                .collect();
            let rel = Rel::Pred(pred);
            stmts.push(FlatStmt::SurjThen(FlatSurjThenStmt::Relation(
                FlatSurjThenStmtRelation { rel, args },
            )));
        }
    }

    for (func, args, result) in iter_func_app(cod, eqlog) {
        if !eqlog.func_app_in_img(morphism, func, args) {
            let func_args: Vec<FlatVar> = el_list_vec(args, eqlog)
                .into_iter()
                .map(|el| *el_vars.get(&el).unwrap())
                .collect();
            let result = *el_vars.get(&result).unwrap();

            let args = {
                let mut a = func_args;
                a.push(result);
                a
            };

            let rel = Rel::Func(func);
            stmts.push(FlatStmt::SurjThen(FlatSurjThenStmt::Relation(
                FlatSurjThenStmtRelation { rel, args },
            )));
        }
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
) -> Option<FlatNonSurjThenStmt> {
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
                Some((func, el_list_vec(args, eqlog)))
            } else {
                None
            }
        })
        .expect("new element should be the result of func_app");
    assert!(
        func_arg_els
            .iter()
            .copied()
            .all(|arg| img_els.contains(&arg)),
        "Arguments to obtain new element should be in image"
    );

    let func_args = func_arg_els
        .into_iter()
        .map(|el| *el_vars.get(&el).unwrap())
        .collect();
    let result = *el_vars.get(&new_el).unwrap();
    Some(FlatNonSurjThenStmt {
        func,
        func_args,
        result,
    })
}

pub fn flatten(
    rule: RuleDeclNode,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> FlatRule {
    let name = match eqlog.rule_name(rule) {
        Some(ident) => identifiers.get(&ident).unwrap().to_string(),
        None => format!("anonymous_rule_{}", rule.0),
    };
    let el_vars = assign_el_vars(iter_grouped_morphisms(rule, eqlog), eqlog);

    let mut stmts: Vec<FlatStmt> = Vec::new();

    for morphism in iter_grouped_morphisms(rule, eqlog) {
        if eqlog.if_morphism(morphism) {
            let mut fork_blocks = Vec::new();
            if !stmts.is_empty() {
                let mut first_block = stmts;
                first_block.extend(flatten_if_arbitrary(morphism, &el_vars, eqlog));
                fork_blocks.push(first_block);
            }
            fork_blocks.extend(flatten_if_fresh(morphism, &el_vars, eqlog));
            stmts = vec![FlatStmt::Fork(FlatForkStmt {
                blocks: fork_blocks,
            })];
        } else if eqlog.surj_then_morphism(morphism) {
            stmts.extend(flatten_surj_then(morphism, &el_vars, eqlog));
        } else if eqlog.non_surj_then_morphism(morphism) {
            let non_surj_then_stmt = match flatten_non_surj_then(morphism, &el_vars, eqlog) {
                Some(non_surj_then_stmt) => non_surj_then_stmt,
                None => {
                    // In this case, `morphism` is an isomorphism, so nothing needs to be done.
                    continue;
                }
            };

            stmts.push(FlatStmt::NonSurjThen(non_surj_then_stmt));

            let if_blocks = flatten_if_fresh(morphism, &el_vars, eqlog);
            assert_eq!(
                if_blocks.len(),
                1,
                "A non surjective then should only require one block to match"
            );
            let if_block = if_blocks.into_iter().next().unwrap();

            let fork_blocks = vec![stmts, if_block];
            stmts = vec![FlatStmt::Fork(FlatForkStmt {
                blocks: fork_blocks,
            })];
        } else {
            panic!("Every grouped morphism must be either if, surj_then or non_surj_then");
        }
    }

    let var_types = make_var_type_map(&el_vars, eqlog);

    ensure_unique_empty_slice_addresses(&mut stmts);
    FlatRule {
        name,
        stmts,
        var_types,
    }
}
