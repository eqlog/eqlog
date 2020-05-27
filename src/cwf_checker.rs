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

pub fn adjoin_element(cwf: &mut Cwf, tracing: Tracing, sort: CwfSort) -> Element {
    cwf.adjoin_element(sort)
}
pub fn adjoin_row(cwf: &mut Cwf, tracing: Tracing, r: CwfRelation, row: Vec<Element>) {
    cwf.adjoin_rows(r, once(row));
}
pub fn adjoin_op(cwf: &mut Cwf, tracing: Tracing, op: CwfRelation, args: Vec<Element>) -> Element {
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
pub fn close_cwf(cwf: &mut Cwf, tracing: Tracing) {
    let sp_iter = 
        CWF_THEORY.functionalities.iter().map(|(r, sp)| sp)
        .chain(CWF_THEORY.axioms.iter().map(|(seq, sp)| sp));
    close_structure(sp_iter, cwf);
}

impl Scope {
    fn new(cwf: &mut Cwf, tracing: Tracing) -> Self {
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
    adjoin_row(cwf, tracing, CwfRelation::ExtTy, vec![ext_ctx_el, ty_el]);
    adjoin_op(cwf, tracing, CwfRelation::Wkn, vec![ext_ctx_el]); // TODO: why is this needed?
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
    let (def_tm, def_extension) =
        with_args(
            cwf, scope, tracing, should_check, def.args.as_slice(),
            |cwf, mut scope, tracing, should_check| {
                let def_ty = add_type(cwf, &mut scope, tracing, should_check, &def.ty);
                let def_tm = add_term(cwf, &mut scope, tracing, should_check, &def.tm);
                let def_tm_ty = tm_ty(cwf, tracing, def_tm);

                if should_check == EqChecking::Yes {
                    close_cwf(cwf, tracing);
                    assert!(
                        els_are_equal(cwf, def_ty, def_tm_ty),
                        "Def body `{:?}` does not have type `{:?}`", def.tm, def.ty
                    );
                }

                (def_tm, scope.current_extension)
            }
        );

    scope.defs.insert(def.name.clone(), (def_extension, def_tm));
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

            // TODO: checking `dom != dom_root_ctx` shouldn't be neccessary once IterExtCtx can be
            // made reflexive
            if dom != dom_root_ctx {
                // return None if dom is not an iterated ext of dom_root_ctx
                cwf.rows(CwfRelation::IterExtCtx).find(|r| r == &[dom_root_ctx, dom])?;
            }

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
        ast::Ty::Unit => {
            adjoin_op(cwf, tracing, CwfRelation::Unit, vec![current_ctx(scope)])
        },
        ast::Ty::Bool => {
            adjoin_op(cwf, tracing, CwfRelation::Bool, vec![current_ctx(scope)])
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
        ast::Tm::BoolElim{discriminee, into_var, into_ty, true_case, false_case} => {
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

            let elim_el = adjoin_op(
                cwf,
                tracing,
                CwfRelation::BoolElim,
                vec![into_ty_el, true_case_el, false_case_el]
            );
            let subst_discriminee_el = add_substitution(
                cwf,
                scope,
                tracing,
                should_check,
                &into_ty_extension,
                &[*discriminee.clone()],
            );

            adjoin_op(cwf, tracing, CwfRelation::SubstTm, vec![subst_discriminee_el, elim_el])
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
def negtrue : Bool :=
  elim true into (x : Bool) : Bool
  | true => false
  | false => true
  end.

def r : negtrue = false :=
  refl false.")
    }

    #[test]
    fn neg_neg_substitution() {
        check_defs("
def foo (x : Bool) : Bool :=
  let b (y : Bool) : Bool := neg (neg y) in
  let r : false = neg true := refl false in
  let s : true = b true := refl true in
  true.")
    }

    #[test]
    fn neg_involutive() {
        check_defs("
def r (x : Bool) : x = neg (neg x) :=
  elim x into (y : Bool) : y = neg (neg y)
  | true => let _0 : false = neg true := refl false in
            (refl true : true = neg (neg true))
  | false => let _1 : true = neg false := refl true in
             (refl false : false = neg (neg false))
  end.")
    }

    #[test]
    fn bool_elim_neg() {
        check_defs("
def neg_ (x : Bool): Bool :=
  elim x into (y : Bool) : Bool
  | true => false
  | false => true
  end.
  
def neg_true : neg_ true = false := refl false.  
  ");
    }
} 
