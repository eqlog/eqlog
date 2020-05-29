use crate::eqlog::element::*;
use crate::eqlog::signature::*;
use crate::eqlog::closure::*;
use crate::cwf::*;
use crate::lang::ast;
use std::collections::{HashSet, HashMap};
use std::iter::once;
use std::convert::TryFrom;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Scope {
    defs: HashMap<String, (Vec<Element>, Element)>, // name => (list of contexts, term)
    current_extension: Vec<Element>, // list of contexts
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EqChecking {
    Yes, // Yes.
    No, // No.
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tracing {
    Yes, // Yes.
    No, // No.
}

pub fn adjoin_element(cwf: &mut Cwf, _tracing: Tracing, sort: CwfSort) -> Element {
    cwf.adjoin_element(sort)
}
pub fn adjoin_row(cwf: &mut Cwf, _tracing: Tracing, r: CwfRelation, row: Vec<Element>) {
    cwf.adjoin_rows(r, once(row));
}
pub fn adjoin_op(cwf: &mut Cwf, _tracing: Tracing, op: CwfRelation, args: Vec<Element>) -> Element {
    assert_eq!(op.relation_kind(), RelationKind::Operation);

    let dom_len: usize = op.arity().len() - 1;
    let op_dom: &[CwfSort] = &op.arity()[.. dom_len];
    let cod: CwfSort = *op.arity().last().unwrap();

    assert!(op_dom.iter().cloned().eq(args.iter().map(|arg| cwf.element_sort(*arg))));

    let result = cwf.adjoin_element(cod);
    let mut row = args;
    row.push(result);
    cwf.adjoin_rows(op, once(row));
    result
}
pub fn close_cwf(cwf: &mut Cwf, _tracing: Tracing) {
    let sp_iter = 
        CWF_THEORY.functionalities.iter().map(|(_, sp)| sp)
        .chain(CWF_THEORY.axioms.iter().map(|(_, sp)| sp));
    close_structure(sp_iter, cwf);
    for ctx in cwf.sort_elements(CwfSort::Ctx) {
        assert_eq!(
            cwf.representative_const(ctx), ctx,
            "Contexts equated",
        );
    }

}

impl Scope {
    pub fn new(cwf: &mut Cwf, tracing: Tracing) -> Self {
        let empty_ctx = adjoin_element(cwf, tracing, CwfSort::Ctx);
        adjoin_op(cwf, tracing, CwfRelation::Id, vec![empty_ctx]);
        Scope {
            defs: HashMap::new(),
            current_extension: vec![empty_ctx],
        }
    }
}


pub fn tm_ty(cwf: &mut Cwf, tracing: Tracing, tm: Element) -> Element {
    adjoin_op(cwf, tracing, CwfRelation::TmTy, vec![tm])
}

pub fn els_are_equal(cwf: &mut Cwf, lhs: Element, rhs: Element) -> bool {
    assert_eq!(cwf.element_sort(lhs), cwf.element_sort(rhs));
    cwf.representative(lhs) == cwf.representative(rhs)
}


pub fn current_ctx(scope: &Scope) -> Element {
    *scope.current_extension.last().unwrap()
}

// Adjoin an opaque term of of type `ty`, but do not change current_ctx or the `Var` relation
// This should only every be called if current_ctx is the empty/initial context
pub fn extend_cwf_checked(
    cwf: &mut Cwf,
    scope: &mut Scope,
    tracing: Tracing,
    var_name: String,
    ty: &ast::Ty,
) {
    assert_eq!(
        scope.current_extension.len(), 1,
        "Called extend_cwf_checked without being in the empty context"
    );
    let ty_el = add_type(cwf, scope, tracing, EqChecking::Yes, ty);
    let var_el = adjoin_element(cwf, tracing, CwfSort::Tm);
    adjoin_row(cwf, tracing, CwfRelation::TmTy, vec![var_el, ty_el]);
    scope.defs.insert(var_name, (scope.current_extension.clone(), var_el));
}

// Adjoin an new context extension by `ty` and adjoin the appropriate `Var` term
pub fn extend_ctx_unchecked(
    cwf: &mut Cwf,
    scope: &mut Scope,
    tracing: Tracing,
    var_name: String,
    ty: &ast::Ty,
) {
    let ty_el = add_type(cwf, scope, tracing, EqChecking::No, ty);
    let ext_ctx_el = adjoin_element(cwf, tracing, CwfSort::Ctx);
    adjoin_row(cwf, tracing, CwfRelation::ExtCtx, vec![current_ctx(scope), ext_ctx_el]);
    adjoin_op(cwf, tracing, CwfRelation::Id, vec![ext_ctx_el]);
    adjoin_op(cwf, tracing, CwfRelation::Wkn, vec![ext_ctx_el]);
    adjoin_row(cwf, tracing, CwfRelation::IterExtCtx, vec![current_ctx(scope), ext_ctx_el]);
    adjoin_row(cwf, tracing, CwfRelation::ExtTy, vec![ext_ctx_el, ty_el]);
    let var_el = adjoin_op(cwf, tracing, CwfRelation::Var, vec![ext_ctx_el]);

    scope.current_extension.push(ext_ctx_el);
    scope.defs.insert(var_name, (scope.current_extension.clone(), var_el));
}

// Run a function that checks a piece of syntax that contains free variables. The function
// takes a modified Scope and Cwf.
fn with_args<R>(
    cwf: &mut Cwf,
    scope: &mut Scope,
    tracing: Tracing,
    should_check: EqChecking,
    args: &[(String, ast::Ty)],
    f: impl Fn (&mut Cwf, Scope, Tracing, EqChecking) -> R,
) -> R {
    if should_check == EqChecking::Yes {
        let mut tmp_cwf = cwf.clone();
        let mut tmp_scope = scope.clone();
        for (arg_name, arg_ty) in args {
            extend_cwf_checked(
                &mut tmp_cwf,
                &mut tmp_scope,
                tracing,
                arg_name.to_string(),
                arg_ty,
            );
        }
        f(&mut tmp_cwf, tmp_scope, tracing, EqChecking::Yes);
    }

    let mut tmp_scope = scope.clone();
    for (arg_name, arg_ty) in args {
        extend_ctx_unchecked(
            cwf,
            &mut tmp_scope,
            tracing,
            arg_name.to_string(),
            arg_ty,
        );
    }
    f(cwf, tmp_scope, tracing, EqChecking::No)
}
 
pub fn add_definition(
    cwf: &mut Cwf,
    scope: &mut Scope,
    tracing: Tracing,
    should_check: EqChecking,
    def: &ast::Def,
) {
    match def {
        ast::Def::Def{name, args, ty, tm} => {
            let (def_tm, def_extension) = with_args(
                cwf, scope, tracing, should_check, args.as_slice(),
                |cwf, mut scope, tracing, should_check| {
                    let def_ty = add_type(cwf, &mut scope, tracing, should_check, &ty);
                    let def_tm = add_term(cwf, &mut scope, tracing, should_check, &tm);
                    let def_tm_ty = tm_ty(cwf, tracing, def_tm);

                    if should_check == EqChecking::Yes {
                        close_cwf(cwf, tracing);
                        assert!(
                            els_are_equal(cwf, def_ty, def_tm_ty),
                            "Def body `{:?}` does not have type `{:?}`", tm, ty
                        );
                    }

                    (def_tm, scope.current_extension)
                },
            );
            scope.defs.insert(name.clone(), (def_extension, def_tm));
        },
        ast::Def::BoolInd{name, into_var, into_ty, true_case, false_case} => {
            let (into_ty_el, into_ty_extension) = with_args(
                cwf, scope, tracing, should_check, &[(into_var.clone(), ast::Ty::Bool)],
                |cwf, mut scope, tracing, should_check| {
                    let into_ty_el = add_type(cwf, &mut scope, tracing, should_check, into_ty);
                    (into_ty_el, scope.current_extension)
                });

            let true_case_el = add_term(cwf, scope, tracing, should_check, true_case);
            let false_case_el = add_term(cwf, scope, tracing, should_check, false_case);

            let true_case_ty_el = tm_ty(cwf, tracing, true_case_el);
            let false_case_ty_el = tm_ty(cwf, tracing, false_case_el);

            let subst_true_el = add_substitution(
                cwf,
                scope,
                tracing,
                should_check,
                &into_ty_extension,
                &[ast::Tm::True],
            );
            let subst_false_el = add_substitution(
                cwf,
                scope,
                tracing,
                should_check,
                &into_ty_extension,
                &[ast::Tm::False],
            );

            let into_ty_true_el = adjoin_op(
                cwf,
                tracing,
                CwfRelation::SubstTy,
                vec![subst_true_el, into_ty_el],
            );
            let into_ty_false_el = adjoin_op(
                cwf,
                tracing,
                CwfRelation::SubstTy,
                vec![subst_false_el, into_ty_el],
            );

            if should_check == EqChecking::Yes {
                close_cwf(cwf, tracing);

                assert!(
                    els_are_equal(cwf, true_case_ty_el, into_ty_true_el),
                    "Term {:?} does not have type {:?}[{:?} := {:?}]", true_case, into_ty, into_var, "True"
                );
                assert!(
                    els_are_equal(cwf, false_case_ty_el, into_ty_false_el),
                    "Term {:?} does not have type {:?}[{:?} := {:?}]", false_case, into_ty, into_var, "False"
                );
            }

            let (elim_el, result_extension) = with_args(
                cwf, scope, tracing, EqChecking::No, &[(into_var.clone(), ast::Ty::Bool)],
                |cwf, mut scope, tracing, should_check| {
                    let rename_mor_el = add_substitution(
                        cwf,
                        &mut scope,
                        tracing,
                        should_check,
                        &into_ty_extension,
                        &[ast::Tm::App{fun: into_var.clone(), args: vec![]}],
                    );
                    let into_ty_subst = adjoin_op(
                        cwf,
                        tracing,
                        CwfRelation::SubstTy,
                        vec![rename_mor_el, into_ty_el],
                    );
                    let elim_el = adjoin_op(
                        cwf,
                        tracing,
                        CwfRelation::BoolElim,
                        vec![into_ty_el, true_case_el, false_case_el, current_ctx(&scope)],
                    );
                    adjoin_row(
                        cwf,
                        tracing,
                        CwfRelation::TmTy,
                        vec![elim_el, into_ty_subst],
                    );

                    (elim_el, scope.current_extension)
                },
            );

            scope.defs.insert(name.clone(), (result_extension, elim_el));
        },
        ast::Def::NatInd{
            name,
            into_var,
            into_ty,
            zero_case,
            succ_nat_var,
            succ_hyp_var,
            succ_hyp_ty,
            succ_tm,
        } => {
            let (into_ty_el, into_ty_extension) = with_args(
                cwf, scope, tracing, should_check, &[(into_var.clone(), ast::Ty::Nat)],
                |cwf, mut scope, tracing, should_check| {
                    let into_ty_el = add_type(cwf, &mut scope, tracing, should_check, into_ty);
                    (into_ty_el, scope.current_extension)
                });

            let zero_case_el = add_term(cwf, scope, tracing, should_check, zero_case);
            let zero_case_ty_el = tm_ty(cwf, tracing, zero_case_el);
            let subst_zero_el = add_substitution(
                cwf,
                scope,
                tracing,
                should_check,
                &into_ty_extension,
                &[ast::Tm::Z],
            );
            let into_ty_zero_el = adjoin_op(
                cwf,
                tracing,
                CwfRelation::SubstTy,
                vec![subst_zero_el, into_ty_el],
            );
            if should_check == EqChecking::Yes {
                close_cwf(cwf, tracing);

                assert!(
                    els_are_equal(cwf, zero_case_ty_el, into_ty_zero_el),
                    "Term {:?} does not have type {:?}[{:?} := 0]",
                    zero_case, into_ty, into_var,
                );
            }

            let (succ_case_el, succ_case_extension) = with_args(
                cwf, scope, tracing, should_check,
                // TODO: check whether succ_hyp_ty is into_ty[into_var := succ_var]
                &[(succ_nat_var.clone(), ast::Ty::Nat), (succ_hyp_var.clone(), succ_hyp_ty.clone())],
                |cwf, mut scope, tracing, should_check| {
                    let succ_case_el = add_term(cwf, &mut scope, tracing, should_check, succ_tm);
                    let succ_tm_ty_el = tm_ty(cwf, tracing, succ_case_el);

                    let succ_var_tm = ast::Tm::App{fun: succ_nat_var.clone(), args: vec![]};
                    let subst_succ_el = add_substitution(
                        cwf, &mut scope, tracing, should_check,
                        &into_ty_extension,
                        &[ast::Tm::S(Box::new(succ_var_tm))],
                    );
                    let into_ty_succ_el = adjoin_op(
                        cwf, tracing,
                        CwfRelation::SubstTy,
                        vec![subst_succ_el, into_ty_el],
                    );
                    if should_check == EqChecking::Yes {
                        close_cwf(cwf, tracing);

                        assert!(
                            els_are_equal(cwf, succ_tm_ty_el, into_ty_succ_el),
                            "Term {:?} does not have type {:?}[{} := S {}]",
                            succ_tm, into_ty, into_var, succ_nat_var,
                        );
                    }

                    (succ_case_el, scope.current_extension)
                },
            );

            let (ind_el, result_extension) = with_args(
                cwf, scope, tracing, EqChecking::No,
                &[(into_var.clone(), ast::Ty::Nat)],
                |cwf, mut scope, tracing, should_check| {
                    let rename_mor_el = add_substitution(
                        cwf, &mut scope, tracing, should_check,
                        &into_ty_extension,
                        &[ast::Tm::App{fun: into_var.clone(), args: vec![]}],
                    );
                    let into_ty_subst = adjoin_op(
                        cwf, tracing,
                        CwfRelation::SubstTy,
                        vec![rename_mor_el, into_ty_el],
                    );
                    let ind_el = adjoin_op(
                        cwf, tracing,
                        CwfRelation::Ind,
                        vec![into_ty_el, zero_case_el, succ_case_el, current_ctx(&scope)],
                    );
                    adjoin_row(
                        cwf,
                        tracing,
                        CwfRelation::TmTy,
                        vec![ind_el, into_ty_subst],
                    );

                    let _subst_hyp_el = add_substitution(
                        cwf, &mut scope, tracing, should_check,
                        &succ_case_extension,
                        &[
                            ast::Tm::App{fun: into_var.clone(), args: vec![]},
                            ast::Tm::AlreadyAdded(ind_el),
                        ],
                    );

                    (ind_el, scope.current_extension)
                },
            );

            scope.defs.insert(name.clone(), (result_extension, ind_el));
        },
    }

}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct MorphismWithSignature {
    pub morph: Element,
    pub dom: Element,
    pub cod: Element,
}

fn adjoin_post_compositions_step(
    cwf: &mut Cwf,
    tracing: Tracing,
    dom_root_ctx: Element,
    after_morphisms: impl IntoIterator<Item = MorphismWithSignature> + Clone,
) -> Vec<MorphismWithSignature> {

    let before_morphisms: Vec<MorphismWithSignature> =
        cwf.rows(CwfRelation::Dom)
        .filter_map(|dom_row| {
            let [morph, dom] = <[Element; 2]>::try_from(dom_row).unwrap();

            // TODO: why doesn't this work?
            // if cwf.rows(CwfRelation::IterExtCtx).find(|r| r == &[dom_root_ctx, dom]).is_none() {
            //     return None;
            // }

            let cod = cwf.rows(CwfRelation::Cod).find(|r| r[0] == morph)?[1];

            Some(MorphismWithSignature{
                morph: morph,
                dom: dom,
                cod: cod,
            })
        })
        .collect();

    let composition_exists: HashSet<(Element, Element)> =
        cwf.rows(CwfRelation::Comp)
        .map(|r| (r[0], r[1]))
        .collect();

    let mut v = Vec::new();
    for before in before_morphisms.iter() {
        for after in after_morphisms.clone() {
            if after.dom != before.cod || composition_exists.contains(&(after.morph, before.morph)) {
                continue
            }

            let comp = adjoin_op(cwf, tracing, CwfRelation::Comp, vec![after.morph, before.morph]);
            v.push(MorphismWithSignature{
                morph: comp,
                dom: before.dom,
                cod: after.cod,
            });
        }
    }
    v
}

pub fn adjoin_post_compositions(
    cwf: &mut Cwf,
    tracing: Tracing,
    dom_root_ctx: Element,
    after_morphisms: impl IntoIterator<Item = MorphismWithSignature>,
) {

    let mut after_morphisms: Vec<MorphismWithSignature> = after_morphisms.into_iter().collect();

    while !after_morphisms.is_empty() {
        close_cwf(cwf, tracing);
        for m in after_morphisms.iter_mut() {
            m.morph = cwf.representative(m.morph);
            m.dom = cwf.representative(m.dom);
            m.cod = cwf.representative(m.cod);
        }
        after_morphisms = adjoin_post_compositions_step(
            cwf,
            tracing,
            dom_root_ctx,
            after_morphisms,
        );
    }
}
 
pub fn add_substitution(
    cwf: &mut Cwf,
    scope: &mut Scope,
    tracing: Tracing,
    should_check: EqChecking,
    dom_extension: &[Element],
    args: &[ast::Tm],
) -> Element {

    let shared_context_len: usize =
        dom_extension.iter().zip(&scope.current_extension).
        take_while(|(lhs, rhs)| lhs == rhs).
        count();

    let shared_extension = &scope.current_extension[.. shared_context_len];
    let last_shared_ctx: Element = *shared_extension.last().unwrap();

    let cur_unshared = &scope.current_extension[shared_context_len ..];
    let dom_unshared = &dom_extension[shared_context_len ..];

    assert!(
        dom_unshared.len() == args.len(),
        "Need `{}` arguments but `{}` are provided",
        dom_unshared.len(), args.len()
    );

    let last_shared_identity: Element =
        adjoin_op(cwf, tracing, CwfRelation::Id, vec![last_shared_ctx]);
    let wkn_shared_to_cur =
        cur_unshared.iter().
        fold(last_shared_identity, |prev, ext| {
            let wkn = adjoin_op(cwf, tracing, CwfRelation::Wkn, vec![*ext]);
            adjoin_op(cwf, tracing, CwfRelation::Comp, vec![wkn, prev])
        });

    let subst =
        dom_unshared.to_vec().iter(). // TODO: can we get rid of to_vec somehow?
        zip(args.iter()).
        fold(wkn_shared_to_cur, |prev_subst, (next_ext, next_arg)| {
            let required_ty = adjoin_op(cwf, tracing, CwfRelation::ExtTy, vec![*next_ext]);
            let required_ty_subst =
                adjoin_op(cwf, tracing, CwfRelation::SubstTy, vec![prev_subst, required_ty]);
            let arg_el = add_term(cwf, scope, tracing, should_check, &next_arg);
            let arg_ty_el = tm_ty(cwf, tracing, arg_el);
            if should_check == EqChecking::Yes {
                close_cwf(cwf, tracing);
                assert!(
                    els_are_equal(cwf, required_ty_subst, arg_ty_el),
                    "The type of term `{:?}` does not equal the type required",
                    next_arg
                );
            }
            adjoin_op(cwf, tracing, CwfRelation::MorExt, vec![*next_ext, prev_subst, arg_el],
            )
        });

    adjoin_post_compositions(
        cwf,
        tracing,
        *dom_extension.last().unwrap(),
        once(MorphismWithSignature{
            morph: subst,
            dom: *dom_extension.last().unwrap(),
            cod: current_ctx(scope),
        })
    );
    
    subst
}

pub fn add_type(
    cwf: &mut Cwf,
    scope: &mut Scope,
    tracing: Tracing,
    should_check: EqChecking, ty: &ast::Ty
) -> Element {
    match ty {
        ast::Ty::AlreadyAdded(el) => {
            assert_eq!(cwf.element_sort(*el), CwfSort::Ty);
            *el
        }
        ast::Ty::Unit => {
            adjoin_op(cwf, tracing, CwfRelation::Unit, vec![current_ctx(scope)])
        },
        ast::Ty::Bool => {
            adjoin_op(cwf, tracing, CwfRelation::Bool, vec![current_ctx(scope)])
        },
        ast::Ty::Nat => {
            adjoin_op(cwf, tracing, CwfRelation::Nat, vec![current_ctx(scope)])
        },
        ast::Ty::Eq(lhs, rhs) => {
            let lhs_el = add_term(cwf, scope, tracing, should_check, lhs);
            let rhs_el = add_term(cwf, scope, tracing, should_check, rhs);

            let lhs_ty_el = tm_ty(cwf, tracing, lhs_el);
            let rhs_ty_el = tm_ty(cwf, tracing, rhs_el);

            if should_check == EqChecking::Yes {
                close_cwf(cwf, tracing);

                assert!(
                    els_are_equal(cwf, lhs_ty_el, rhs_ty_el),
                    "Terms do not have the same type: `{:?}` and `{:?}`", lhs, rhs,
                );
            }

            adjoin_op(cwf, tracing, CwfRelation::Eq, vec![lhs_el, rhs_el])
        },
    }
}
pub fn add_term(
    cwf: &mut Cwf,
    scope: &mut Scope,
    tracing: Tracing,
    should_check: EqChecking,
    tm: &ast::Tm
) -> Element {
    match tm {
        ast::Tm::AlreadyAdded(el) => {
            assert_eq!(cwf.element_sort(*el), CwfSort::Tm);
            *el
        },
        ast::Tm::Typed{tm, ty} => {
            let ty_el = add_type(cwf, scope, tracing, should_check, ty);
            let tm_el = add_term(cwf, scope, tracing, should_check, tm);
            // or the other way round?
            let tm_el_ty = tm_ty(cwf, tracing, tm_el);

            if should_check == EqChecking::Yes {
                close_cwf(cwf, tracing);
                assert!(
                    els_are_equal(cwf, ty_el, tm_el_ty),
                    "Term `{:?}` does not have type `{:?}`", tm, ty
                );
            }
            tm_el
        },
        ast::Tm::App{fun, args} => {
            let def =
                scope.defs.get(fun).
                unwrap_or_else(|| panic!("`{}` is undefined", fun));
            let def_extension: Vec<Element> = def.0.clone();
            let def_el: Element = def.1;

            let subst_el = add_substitution(
                cwf,
                scope,
                tracing,
                should_check,
                &def_extension,
                args,
            );

            adjoin_op(cwf, tracing, CwfRelation::SubstTm, vec![subst_el, def_el])
        },
        ast::Tm::Let{body, result} => {
            let mut tmp_scope = scope.clone();
            for def in body {
                add_definition(cwf, &mut tmp_scope, tracing, should_check, &def);
            }
            add_term(cwf, &mut tmp_scope, tracing, should_check, result)
        },
        ast::Tm::UnitTm => {
            adjoin_op(cwf, tracing, CwfRelation::UnitTm, vec![current_ctx(scope)])
        },
        ast::Tm::True => {
            adjoin_op(cwf, tracing, CwfRelation::True, vec![current_ctx(scope)])
        },
        ast::Tm::False => {
            adjoin_op(cwf, tracing, CwfRelation::False, vec![current_ctx(scope)])
        },
        ast::Tm::Neg(arg) => {
            let arg_el = add_term(cwf, scope, tracing, should_check, arg);
            let arg_ty_el = tm_ty(cwf, tracing, arg_el);
            let bool_el = adjoin_op(cwf, tracing, CwfRelation::Bool, vec![current_ctx(scope)]);
            if should_check == EqChecking::Yes {
                close_cwf(cwf, tracing);
                assert!(
                    els_are_equal(cwf, arg_ty_el, bool_el),
                    "{:?} must be of type bool", arg,
                );
            }
            adjoin_op(cwf, tracing, CwfRelation::Neg, vec![arg_el])
        },
        ast::Tm::Refl(arg) => {
            let arg_el = add_term(cwf, scope, tracing, should_check, arg);
            adjoin_op(cwf, tracing, CwfRelation::Refl, vec![arg_el])
        },
        ast::Tm::Z => {
            adjoin_op(cwf, tracing, CwfRelation::Z, vec![current_ctx(scope)])
        },
        ast::Tm::S(arg) => {
            let arg_el = add_term(cwf, scope, tracing, should_check, arg);
            let arg_ty = tm_ty(cwf, tracing, arg_el);
            let nat_ty = adjoin_op(cwf, tracing, CwfRelation::Nat, vec![current_ctx(scope)]);
            if should_check == EqChecking::Yes {
                close_cwf(cwf, tracing);
                assert!(
                    els_are_equal(cwf, arg_ty, nat_ty),
                    "Term {:?} does not have type Nat", arg,
                );
            }

            adjoin_op(cwf, tracing, CwfRelation::S, vec![arg_el])
        },
    }
}

#[cfg(test)]
mod test {
    use crate::lang::parser;
    use super::*;
    use parser::*;

    fn check_defs(text: &str) {
        let unit =
            match UnitParser::new().parse(text) {
                Ok(result) => result,
                Err(err) => panic!("{}", err)
            };
        let tracing = Tracing::Yes;
        let mut cwf = Cwf::new(CwfSignature::new());
        let mut scope = Scope::new(&mut cwf, tracing);
        for def in &unit {
            add_definition(&mut cwf, &mut scope, tracing, EqChecking::Yes, &def)
        }
    }

    #[test]
    fn test_bool_identity() {
        check_defs("def id (x : Bool) : Bool := x.")
    }

    #[test]
    fn test_bool_identity_asserted() {
        check_defs("def id (x : Bool) : Bool := (x : Bool).")
    }

    #[test] #[should_panic]
    fn test_ill_typed_def() {
        check_defs("def x : Bool := unit.")
    }

    #[test] #[should_panic]
    fn test_failing_assertion() {
        check_defs("def x : Bool := (True: Unit).")
    }

    #[test]
    fn test_unit_tm_uniqueness() {
        check_defs("
def r (x y : Unit) : x = y :=
    refl unit.")
    }

    #[test] #[should_panic]
    fn test_refl_ill_typed() {
        check_defs("
def r : true = true :=
  (refl true : true = true).

def r' : Bool := refl true.")
    }

    #[test]
    fn test_refl_of_var() {
        check_defs("def r (x : Bool) : x = x := refl x.")
    }

    #[test]
    fn test_subst_of_refl_of_var() {
        check_defs("
def r (x : Bool) : x = x :=
  refl x.

def rtrue : true = true :=
  r true.")
    }

    #[test]
    fn test_neg_of_true() {
        check_defs("
def negtrue : Bool :=
  neg true.
def r : negtrue = false :=
  refl false.")
    }

    #[test]
    fn bool_elim_neg_true() {
        check_defs("
bool_ind neg_ (x : Bool) : Bool
  | true => false
  | false => true
  .

def r : neg_ true = false :=
  refl false.")
    }

    #[test]
    fn neg_neg_substitution() {
        check_defs("
def foo (x : Bool) : Bool :=
  let
    def b (y : Bool) : Bool := neg (neg y).
    def r : false = neg true := refl false.
    def s : true = b true := refl true.
  in
    true.")
    }

    #[test]
    fn neg_involutive() {
        check_defs("
bool_ind r (x : Bool) : x = neg (neg x)
  | true =>
      let
        def _0 : false = neg true := refl false.
      in
        (refl true : true = neg (neg true))
  | false =>
      let
        def _1 : true = neg false := refl true.
      in
        (refl false : false = neg (neg false))
  .
")
    }

    #[test]
    fn bool_elim_neg_involutive() {
        check_defs("
bool_ind neg_ (x : Bool) : Bool
  | true => false
  | false => true
  .

bool_ind r (x : Bool) : x = neg_ (neg_ x)
  | true =>
      let
        def _0 : false = neg_ true := refl false.
      in
        (refl true : true = neg_ (neg_ true))
  | false =>
      let
        def _1 : true = neg_ false := refl true.
      in
        (refl false : false = neg_ (neg_ false))
  .
")
    }

    #[test]
    fn and_table() {
        check_defs("
def and (x: Bool) (y: Bool) : Bool :=
  let
    bool_ind elim (z : Bool) : Bool
    | true => y
    | false => false
    .
  in
    elim x
  .

def true_true : Bool := and true true.
def r0 : true_true = true := refl true.
def true_false : Bool := and true false.
def r1 : true_false = false := refl false.
def false_true : Bool := and true false.
def r2 : false_true = false := refl false.
def false_false : Bool := and true false.
def r3 : false_false = false := refl false.
")
    }

    #[test]
    fn de_morgan() {
        check_defs("
def and (x: Bool) (y: Bool) : Bool :=
  let
    bool_ind elim (z : Bool) : Bool
      | true => y
      | false => false
      .
  in
    elim x
  .
def or (x: Bool) (y: Bool) : Bool :=
  let
    bool_ind elim (z : Bool) : Bool
      | true => true
      | false => y
      .
  in
    elim x
  .
bool_ind neg_ (x : Bool) : Bool
  | true => false
  | false => true
  .


def _0 : neg_ false = true := refl true.
def _1 : neg_ true = false := refl false.
def _2 : and true true = true := refl true.
def _3 : and true false = false := refl false.
def _4 : and false true = false := refl false.
def _5 : and false false = false := refl false.

def r (x: Bool) (y : Bool) : neg_ (and x y) = or (neg_ x) (neg_ y) :=
  let 
    bool_ind elim_x (x0 : Bool) : neg_ (and x0 y) = or (neg_ x0) (neg_ y)
      | true =>
          let
            bool_ind elim_y (y0 : Bool) : neg_ (and true y0) = or (neg_ true) (neg_ y0)
              | true => refl false
              | false => refl true
              .
          in
            (elim_y y : neg_ (and true y) = or (neg_ true) (neg_ y))
      | false =>
          let
            bool_ind elim_y (y0 : Bool) : neg_ (and false y0) = or (neg_ false) (neg_ y0)
              | true => refl true
              | false => refl true
              .
          in
            (elim_y y : neg_ (and false y) = or (neg_ false) (neg_ y))
      .
  in
    elim_x x
  .
")
    }

    #[test]
    fn nat_constants() {
        check_defs("
def zero : Nat := Z.
def one : Nat := S zero.
def two : Nat := S one.
def two_ : Nat := 2.
def r : two = two_ := refl (S (S Z)).
")
    }
    #[test]
    fn nat_ind_succ() {
        check_defs("
nat_ind succ (m : Nat) : Nat
  | Z => S Z
  | (S pred : Nat) (hyp : Nat) => S hyp
  .

def r0 : succ 0 = 1 := refl 1.
def r1 : succ 1 = 2 := refl 2.
def r2 : succ 2 = 3 := refl 3.
")
    }
    #[test]
    fn nat_ind_double() {
        check_defs("
nat_ind double (m : Nat) : Nat
  | Z => Z
  | (S pred : Nat) (hyp : Nat) => S (S hyp)
  .

def r0 : double 0 = 0 := refl 0.
def r1 : double 1 = 2 := refl 2.
def r2 : double 2 = 4 := refl 4.
def r3 : double 3 = 6 := refl 6.
")
    }
    #[test] #[should_panic]
    fn nat_ind_double_wrong() {
        check_defs("
nat_ind double (m : Nat) : Nat
  | Z => Z
  | (S pred : Nat) (hyp : Nat) => S (S hyp)
  .

def r2 : double 2 = 5 := refl 5.
")
    }
}
