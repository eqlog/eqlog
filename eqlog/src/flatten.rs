use crate::eqlog_util::*;
use crate::flat_eqlog::*;
use eqlog_eqlog::*;
use maplit::btreemap;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::pin::Pin;

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
    let mut el_terms = BTreeMap::new();
    let mut available_vars = (0..).map(FlatVar);

    for transition in morphisms {
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
                .or_insert_with(|| available_vars.next().unwrap());
        }
    }

    el_terms
}

fn make_var_type_map(el_vars: &BTreeMap<El, FlatVar>, eqlog: &Eqlog) -> BTreeMap<FlatVar, Type> {
    el_vars
        .iter()
        .map(|(el, var)| {
            let el_typ = el_type(*el, eqlog).unwrap();
            let typ = match eqlog.element_type_case(el_typ) {
                ElementTypeCase::AmbientType(typ) => typ,
                ElementTypeCase::InstantiatedType(_, typ) => typ,
            };
            (*var, typ)
        })
        .collect()
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

    for (rel, els) in iter_rel_app(cod, eqlog) {
        if eqlog.rel_tuple_in_img(morphism, rel, els) {
            continue;
        }

        let model_el: Option<El> = eqlog.rel_app_parent_model_el(rel, els);
        let els_vec: Vec<El> = el_list_vec(els, eqlog);
        let args: Vec<FlatVar> = model_el
            .into_iter()
            .chain(els_vec)
            .map(|el| *el_vars.get(&el).unwrap())
            .collect();

        let age = QueryAge::All;
        stmts.push(FlatStmt::If(FlatIfStmt::Relation(FlatIfStmtRelation {
            rel,
            args,
            age,
        })));
    }

    for el in iter_els(cod, eqlog)
        .filter(move |&el| !eqlog.el_in_img(morphism, el) && !eqlog.constrained_el(el))
    {
        let var = *el_vars.get(&el).unwrap();
        let age = QueryAge::All;
        let el_typ = el_type(el, eqlog).unwrap();
        let (parent_var, typ) = match eqlog.element_type_case(el_typ) {
            ElementTypeCase::AmbientType(typ) => {
                let typ_def_sym_scope = eqlog.type_definition_symbol_scope(typ).unwrap();
                let el_struct = eqlog.el_structure(el).unwrap();
                let model_var = eqlog
                    .ambient_model_el(typ_def_sym_scope, el_struct)
                    .map(|model_el| *el_vars.get(&model_el).unwrap());
                (model_var, typ)
            }
            ElementTypeCase::InstantiatedType(model_el, typ) => {
                let var = Some(*el_vars.get(&model_el).unwrap());
                (var, typ)
            }
        };
        let if_stmt = match parent_var {
            None => FlatIfStmt::Type(FlatIfStmtType { var, age }),
            Some(parent_var) => {
                let parent_rel = eqlog
                    .func_rel(eqlog.parent_model_func(typ).unwrap())
                    .unwrap();
                FlatIfStmt::Relation(FlatIfStmtRelation {
                    rel: parent_rel,
                    args: vec![var, parent_var],
                    age,
                })
            }
        };
        stmts.push(FlatStmt::If(if_stmt));
    }

    stmts
}

/// Returns a list of list of if statements which together match the delta given by `morphism` with
/// fresh data and the domain of `morphism` with arbitrary data.
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

    let mut fresh_type_els: Vec<El> = Vec::new();
    let mut arbitrary_type_els: Vec<El> = Vec::new();

    let cod = eqlog.cod(morphism).expect("cod should be total");

    for (rel, els) in iter_rel_app(cod, eqlog) {
        let model_el: Option<El> = eqlog.rel_app_parent_model_el(rel, els);
        let els_vec: Vec<El> = el_list_vec(els, eqlog);
        let args: Vec<FlatVar> = model_el
            .into_iter()
            .chain(els_vec)
            .map(|el| *el_vars.get(&el).unwrap())
            .collect();

        if eqlog.rel_tuple_in_img(morphism, rel, els) {
            arbitrary_rel_tuples.push((rel, args));
        } else {
            fresh_rel_tuples.push((rel, args));
        }
    }

    for el in iter_els(cod, eqlog).filter(|el| !eqlog.constrained_el(*el)) {
        let in_img = eqlog.el_in_img(morphism, el);
        if in_img {
            arbitrary_type_els.push(el);
        } else {
            fresh_type_els.push(el);
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
            let age = match i.cmp(&fresh_rel_index) {
                Ordering::Less => QueryAge::All,
                Ordering::Equal => QueryAge::New,
                Ordering::Greater => QueryAge::Old,
            };
            block.push(FlatStmt::If(FlatIfStmt::Relation(FlatIfStmtRelation {
                rel,
                args,
                age,
            })));
        }

        for el in fresh_type_els
            .iter()
            .chain(arbitrary_type_els.iter())
            .copied()
        {
            let age = QueryAge::All;
            let var = *el_vars.get(&el).unwrap();
            let el_typ = el_type(el, eqlog).unwrap();
            let (parent_var, typ) = match eqlog.element_type_case(el_typ) {
                ElementTypeCase::AmbientType(typ) => {
                    let typ_def_sym_scope = eqlog.type_definition_symbol_scope(typ).unwrap();
                    let el_struct = eqlog.el_structure(el).unwrap();
                    let model_var = eqlog
                        .ambient_model_el(typ_def_sym_scope, el_struct)
                        .map(|model_el| *el_vars.get(&model_el).unwrap());
                    (model_var, typ)
                }
                ElementTypeCase::InstantiatedType(model_el, typ) => {
                    let var = Some(*el_vars.get(&model_el).unwrap());
                    (var, typ)
                }
            };
            let if_stmt = match parent_var {
                None => FlatIfStmt::Type(FlatIfStmtType { var, age }),
                Some(parent_var) => {
                    let parent_rel = eqlog
                        .func_rel(eqlog.parent_model_func(typ).unwrap())
                        .unwrap();
                    FlatIfStmt::Relation(FlatIfStmtRelation {
                        rel: parent_rel,
                        args: vec![var, parent_var],
                        age,
                    })
                }
            };
            block.push(FlatStmt::If(if_stmt));
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
            let age = QueryAge::Old;
            block.push(FlatStmt::If(FlatIfStmt::Relation(FlatIfStmtRelation {
                rel,
                args,
                age,
            })));
        }

        for (i, el) in fresh_type_els
            .iter()
            .chain(arbitrary_type_els.iter())
            .copied()
            .enumerate()
        {
            let age = match i.cmp(&fresh_type_el_index) {
                Ordering::Less => QueryAge::All,
                Ordering::Equal => QueryAge::New,
                Ordering::Greater => QueryAge::Old,
            };
            let var = *el_vars.get(&el).unwrap();
            let el_typ = el_type(el, eqlog).unwrap();
            let (parent_var, typ) = match eqlog.element_type_case(el_typ) {
                ElementTypeCase::AmbientType(typ) => {
                    let typ_def_sym_scope = eqlog.type_definition_symbol_scope(typ).unwrap();
                    let el_struct = eqlog.el_structure(el).unwrap();
                    let model_var = eqlog
                        .ambient_model_el(typ_def_sym_scope, el_struct)
                        .map(|model_el| *el_vars.get(&model_el).unwrap());
                    (model_var, typ)
                }
                ElementTypeCase::InstantiatedType(model_el, typ) => {
                    let var = Some(*el_vars.get(&model_el).unwrap());
                    (var, typ)
                }
            };
            let if_stmt = match parent_var {
                None => FlatIfStmt::Type(FlatIfStmtType { var, age }),
                Some(parent_var) => {
                    let parent_rel = eqlog
                        .func_rel(eqlog.parent_model_func(typ).unwrap())
                        .unwrap();
                    FlatIfStmt::Relation(FlatIfStmtRelation {
                        rel: parent_rel,
                        args: vec![var, parent_var],
                        age,
                    })
                }
            };
            block.push(FlatStmt::If(if_stmt));
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

    for (rel, els) in iter_rel_app(cod, eqlog) {
        if eqlog.rel_tuple_in_img(morphism, rel, els) {
            continue;
        }

        let model_el: Option<El> = eqlog.rel_app_parent_model_el(rel, els);
        let els_vec: Vec<El> = el_list_vec(els, eqlog);
        let args: Vec<FlatVar> = model_el
            .into_iter()
            .chain(els_vec)
            .map(|el| *el_vars.get(&el).unwrap())
            .collect();

        stmts.push(FlatStmt::SurjThen(FlatSurjThenStmt::Relation(
            FlatSurjThenStmtRelation { rel, args },
        )));
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
        .map(|el| *el_vars.get(&el).unwrap())
        .collect();

    let result = *el_vars.get(&new_el).unwrap();
    Some(FlatNonSurjThenStmt {
        func,
        func_args: flat_func_args,
        result,
    })
}

/// Compiles an Eqlog [RuleDeclNode] into a [FlatRule].
fn flatten_rule(
    rule: RuleDeclNode,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> FlatRule {
    let name = match eqlog.rule_name(rule) {
        Some(ident) => identifiers.get(&ident).unwrap().to_string(),
        None => format!("anonymous_rule_{}", rule.0),
    };

    let el_vars = assign_el_vars(iter_rule_morphisms(rule, eqlog).flatten(), eqlog);

    // The general strategy is as follows:
    // - The first flat function (with index 0) is the entry point for the flat rule. The body of
    //   function 0 consists of call to other functions only. This ensure that we can always append
    //   a call statement to function 0 and be guaranteed that the call is executed precisely once.
    // - During translation, we associate a "matching function" to each structure that occurs as a
    //   domain or codomain of a morphism. The main property of the matching function is such that
    //   by the end of its body, all elements of the corresponding structure have been matched.

    let mut funcs: Vec<FlatFunc> = Vec::new();
    funcs.push(FlatFunc {
        name: FlatFuncName(0),
        args: Vec::new(),
        body: vec![FlatStmt::Call {
            func_name: FlatFuncName(1),
            args: Vec::new(),
        }],
    });

    // The first structure in a rule is always empty, so we can match it using an empty function.
    funcs.push(FlatFunc {
        name: FlatFuncName(1),
        args: Vec::new(),
        body: Vec::new(),
    });
    let mut matching_func_indices: BTreeMap<Structure, usize> =
        btreemap! {eqlog.before_rule_structure(rule).unwrap() => 1};

    for morphism in iter_rule_morphisms(rule, eqlog).flatten() {
        let matching_func_index = *matching_func_indices
            .get(&eqlog.dom(morphism).unwrap())
            .unwrap();
        let should_match_all_data = matching_func_index != 1;

        let cod_flat_vars: Vec<FlatVar> = iter_els(eqlog.cod(morphism).unwrap(), eqlog)
            .map(|el| *el_vars.get(&el).unwrap())
            .collect();

        if eqlog.if_morphism(morphism) {
            let old_if_func_index: Option<usize> = if should_match_all_data {
                // Create a new function that, given a match of the domain of `morphism`, matches the
                // codomain with arbitrary (potentially old) data. We call this function at the end of
                // the function that matches the domain of `morphism` with new data.
                let old_if_func_index = funcs.len();
                let old_if_func_args: Vec<_> = iter_els(eqlog.dom(morphism).unwrap(), eqlog)
                    .map(|el| *el_vars.get(&el).unwrap())
                    .collect();
                let old_if_func = FlatFunc {
                    name: FlatFuncName(funcs.len()),
                    args: old_if_func_args.clone(),
                    body: flatten_if_arbitrary(morphism, &el_vars, eqlog),
                };
                funcs.push(old_if_func);
                funcs[matching_func_index].body.push(FlatStmt::Call {
                    func_name: FlatFuncName(old_if_func_index),
                    args: old_if_func_args,
                });
                Some(old_if_func_index)
            } else {
                None
            };

            // Create functions that match the codomain of `morphism` with new data relative to
            // to the domain if `morphism`.
            // These functions don't take any arguments, and we call them at the entry point, i.e.
            // funcs[0].
            let before_fresh_if_func_len = funcs.len();
            funcs.extend(
                flatten_if_fresh(morphism, &el_vars, eqlog)
                    .into_iter()
                    .zip(before_fresh_if_func_len..)
                    .map(|(body, func_index)| FlatFunc {
                        name: FlatFuncName(func_index),
                        args: Vec::new(),
                        body,
                    }),
            );
            let after_fresh_if_func_len = funcs.len();

            for i in before_fresh_if_func_len..after_fresh_if_func_len {
                funcs[0].body.push(FlatStmt::Call {
                    func_name: FlatFuncName(i),
                    args: Vec::new(),
                });
            }

            // A function that is called from all the matching functions we've created so far.
            let joined_func_index = funcs.len();
            let joined_func = FlatFunc {
                name: FlatFuncName(joined_func_index),
                args: cod_flat_vars.clone(),
                body: Vec::new(),
            };
            let joined_func_name = joined_func.name;
            funcs.push(joined_func);

            for func_index in old_if_func_index
                .into_iter()
                .chain(before_fresh_if_func_len..after_fresh_if_func_len)
            {
                let call = FlatStmt::Call {
                    func_name: FlatFuncName(joined_func_index),
                    args: cod_flat_vars.clone(),
                };
                funcs[func_index].body.push(call);
            }

            matching_func_indices.insert(eqlog.cod(morphism).unwrap(), joined_func_name.0);
        } else if eqlog.surj_then_morphism(morphism) {
            // TODO: We should only execute this unconditionally if should_match_all_data is true.
            // Otherwise, we should only execute it in the first iteration of the first `close`
            // call, i.e. when the empty join is dirty/fresh. The best way to do this is probably
            // to 1. introduce a flat eqlog statement that matches the empty join. Then we can
            // introduce a new function here that matches the empty join and only then executes the
            // flatten_surj_then statements. This function can then be called from function 0.
            funcs[matching_func_index]
                .body
                .extend(flatten_surj_then(morphism, &el_vars, eqlog));
            matching_func_indices.insert(eqlog.cod(morphism).unwrap(), matching_func_index);
        } else if eqlog.non_surj_then_morphism(morphism) {
            let dom_vars: Vec<FlatVar> = iter_els(eqlog.dom(morphism).unwrap(), eqlog)
                .map(|el| *el_vars.get(&el).unwrap())
                .collect();
            let cod_vars: Vec<FlatVar> = iter_els(eqlog.cod(morphism).unwrap(), eqlog)
                .map(|el| *el_vars.get(&el).unwrap())
                .collect();

            let non_surj_then_stmt = match flatten_non_surj_then(morphism, &el_vars, eqlog) {
                Some(non_surj_then_stmt) => non_surj_then_stmt,
                None => {
                    // In this case, `morphism` is an isomorphism, so nothing needs to be done.
                    continue;
                }
            };

            // Create a function that, given a match of the domain of `morphism`, either
            //
            // 1. adjoins the new element to the model so that the codomain matches if no match
            //    is possible (i.e. the new element in the codomain can't be matched), or
            // 2. if a match is possible, matches the codomain with arbitrary (potentially old)
            //    data.
            //
            // This is precisely what the non surjective then statement is supposed to do, so
            // that's the only statement in the body of the function.
            //
            // TODO: We should only execute this unconditionally if should_match_all_data is true.
            // Otherwise, we should only execute it in the first iteration of the first `close`
            // call, i.e. when the empty join is dirty/fresh.
            let non_surj_then_stmt = FlatStmt::NonSurjThen(non_surj_then_stmt);
            let non_surj_then_func_index = funcs.len();
            let non_surj_then_func = FlatFunc {
                name: FlatFuncName(non_surj_then_func_index),
                args: dom_vars.clone(),
                body: vec![non_surj_then_stmt],
            };
            funcs.push(non_surj_then_func);
            funcs[matching_func_index].body.push(FlatStmt::Call {
                func_name: FlatFuncName(non_surj_then_func_index),
                args: dom_vars,
            });

            // Create a function that matches the codomain of `morphism` with fresh data relative
            // to the domain. Since a non-surjective statement is given by at most one new tuple in
            // a relation, it should be possible to match it with fresh data in just one function.
            let mut fresh_if_blocks = flatten_if_fresh(morphism, &el_vars, eqlog).into_iter();
            let fresh_if_block = fresh_if_blocks
                .next()
                .expect("There should be at least one block");
            assert!(
                fresh_if_blocks.next().is_none(),
                "There should be at most one block"
            );

            let fresh_if_func_index = funcs.len();
            let fresh_if_func = FlatFunc {
                name: FlatFuncName(fresh_if_func_index),
                args: Vec::new(),
                body: fresh_if_block,
            };
            funcs.push(fresh_if_func);
            funcs[0].body.push(FlatStmt::Call {
                func_name: FlatFuncName(fresh_if_func_index),
                args: Vec::new(),
            });

            // Finally, create a single function that's called from both the non-surjective then
            // function and the fresh if function we've just created. This will serve as the
            // function that matches the codomain of `morphism` with new data.
            let cont_func_index = funcs.len();
            let cont_func = FlatFunc {
                name: FlatFuncName(cont_func_index),
                args: cod_vars.clone(),
                body: Vec::new(),
            };
            funcs.push(cont_func);

            for func_index in [non_surj_then_func_index, fresh_if_func_index] {
                funcs[func_index].body.push(FlatStmt::Call {
                    func_name: FlatFuncName(cont_func_index),
                    args: cod_vars.clone(),
                });
            }

            matching_func_indices.insert(eqlog.cod(morphism).unwrap(), cont_func_index);
        } else if eqlog.noop_morphism(morphism) {
            matching_func_indices.insert(eqlog.cod(morphism).unwrap(), matching_func_index);
        } else {
            panic!("Every rule morphism must be either if, surj_then or non_surj_then");
        }
    }

    let var_types = make_var_type_map(&el_vars, eqlog);
    FlatRule {
        name,
        funcs,
        var_types,
    }
}

pub struct FlatRules {
    rules_vec: Pin<Box<Vec<FlatRule>>>,
    analyses_vec: Vec<FlatRuleAnalysis<'static>>,
}

impl FlatRules {
    pub fn rules<'a>(&'a self) -> &'a [FlatRule] {
        self.rules_vec.as_slice()
    }
    pub fn analyses<'a>(&'a self) -> &'a [FlatRuleAnalysis<'a>] {
        self.analyses_vec.as_slice()
    }
}

pub fn flatten(eqlog: &Eqlog, identifiers: &BTreeMap<Ident, String>) -> FlatRules {
    let mut rules_vec: Vec<FlatRule> = Vec::new();

    rules_vec.extend(eqlog.iter_func().map(|func| functionality_v2(func, &eqlog)));

    let functionality_rule_num = rules_vec.len();
    rules_vec.extend(eqlog.iter_rule_decl_node().map(|rule| {
        let mut flat_rule = flatten_rule(rule, &eqlog, &identifiers);
        // Necessary here for explicit rules, but not for implicit functionality rules, since the
        // latter are already ordered reasonably.
        sort_if_stmts(&mut flat_rule);
        flat_rule
    }));

    let rules_vec = Box::pin(rules_vec);

    let rules_slice = rules_vec.as_slice();
    let rules_slice =
        unsafe { std::mem::transmute::<&[FlatRule], &'static [FlatRule]>(rules_slice) };
    let (flat_functionality_rules, flat_explicit_rules) =
        rules_slice.split_at(functionality_rule_num);
    let analyses_vec = flat_functionality_rules
        .iter()
        .map(|rule| FlatRuleAnalysis::new(rule, CanAssumeFunctionality::No, eqlog))
        .chain(
            flat_explicit_rules
                .iter()
                .map(|rule| FlatRuleAnalysis::new(rule, CanAssumeFunctionality::Yes, eqlog)),
        )
        .collect();
    FlatRules {
        rules_vec,
        analyses_vec,
    }
}
