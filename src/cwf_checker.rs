use crate::eqlog::element::*;
use crate::cwf::*;
use std::collections::HashMap;
use std::iter::once;
use crate::lang::ast;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Environment {
    defs: HashMap<String, (Vec<Element>, Element)>, // name => (list of contexts, term)
    current_extension: Vec<Element>, // list of contexts
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EqChecking {
    Yes, // Yes.
    No, // No.
}

impl Environment {
    pub fn new(cwf: &mut Cwf) -> Self {
        Environment {
            defs: HashMap::new(),
            current_extension: vec![cwf.adjoin_element(CwfSort::Ctx)],
        }
    }
    fn current_ctx(&self) -> Element {
        *self.current_extension.last().unwrap()
    }
    
    // Adjoin an opaque term of of type `ty`, but do not change current_ctx or the `Var` relation
    // This should only every be called if current_ctx is the empty/initial context
    pub fn extend_cwf_checked(&mut self, cwf: &mut Cwf, var_name: String, ty: &ast::Ty) {
        assert_eq!(
            self.current_extension.len(), 1,
            "Called extend_cwf_checked without being in the empty context"
        );
        let ty_el = self.add_type(cwf, EqChecking::Yes, ty);
        let var_el = cwf.adjoin_element(CwfSort::Tm);
        cwf.adjoin_rows(
            CwfRelation::TmTy,
            once(vec![var_el, ty_el]),
        );
        self.defs.insert(var_name, (self.current_extension.clone(), var_el));
    }

    // Adjoin an new context extension by `ty` and adjoin the appropriate `Var` term
    pub fn extend_ctx_unchecked(&mut self, cwf: &mut Cwf, var_name: String, ty: &ast::Ty) {
        let ty_el = self.add_type(cwf, EqChecking::No, ty);
        let ext_ctx_el = cwf.adjoin_element(CwfSort::Ctx);
        cwf.adjoin_rows(
            CwfRelation::ExtCtx,
            once(vec![self.current_ctx(), ext_ctx_el]),
        );
        cwf.adjoin_rows(
            CwfRelation::ExtTy,
            once(vec![ext_ctx_el, ty_el]),
        );
        adjoin_op(cwf, CwfRelation::Wkn, vec![ext_ctx_el]); // TODO: why is this needed?
        let var_el = adjoin_op(cwf, CwfRelation::Var, vec![ext_ctx_el]);

        self.current_extension.push(ext_ctx_el);
        self.defs.insert(var_name, (self.current_extension.clone(), var_el));
    }

    fn check_with_args<R>(
        mut self,
        mut cwf: Cwf,
        args: &[(String, ast::Ty)],
        f: impl Fn (Environment, &mut Cwf, EqChecking) -> R,
    ) -> R {
        for (arg_name, arg_ty) in args {
            self.extend_cwf_checked(&mut cwf, arg_name.to_string(), arg_ty);
        }
        f(self, &mut cwf, EqChecking::Yes)
    }

    fn unchecked_with_args<R>(
        mut self,
        cwf: &mut Cwf,
        args: &[(String, ast::Ty)],
        f: impl Fn (Environment, &mut Cwf, EqChecking) -> R,
    ) -> R {
        for (arg_name, arg_ty) in args {
            self.extend_ctx_unchecked(cwf, arg_name.to_string(), arg_ty);
        }
        f(self, cwf, EqChecking::No)
    }

    // Run a function that checks a piece of syntax that contains free variables. The function
    // takes a modified Environment and Cwf.
    fn with_args<R>(
        self,
        cwf: &mut Cwf,
        should_check: EqChecking,
        args: &[(String, ast::Ty)],
        f: impl Fn (Environment, &mut Cwf, EqChecking) -> R,
    ) -> R {
        if should_check == EqChecking::Yes {
            self.clone().check_with_args(cwf.clone(), args, &f);
        }

        self.unchecked_with_args(cwf, args, &f)
    }

    pub fn add_definition(&mut self, cwf: &mut Cwf, should_check: EqChecking, def: &ast::Def) {
        let (def_tm, def_extension) = self.clone().with_args(cwf, should_check, def.args.as_slice(),
            |mut extended_self, cwf, should_check| {
                let def_ty = extended_self.add_type(cwf, should_check, &def.ty);
                let def_tm = extended_self.add_term(cwf, should_check, &def.tm);
                let def_tm_ty = tm_ty(cwf, def_tm);

                if should_check == EqChecking::Yes {
                    close_cwf(cwf);
                    assert!(
                        els_are_equal(cwf, def_ty, def_tm_ty),
                        "Def body `{:?}` does not have type `{:?}`", def.tm, def.ty
                    );
                }

                (def_tm, extended_self.current_extension)
            });

        self.defs.insert(def.name.clone(), (def_extension, def_tm));
    }

    pub fn add_substitution(
        &mut self,
        cwf: &mut Cwf,
        should_check: EqChecking,
        dom_extension: &[Element],
        // args: &[Element],
        args: &[ast::Tm],
    ) -> Element {

        let shared_context_len: usize =
            dom_extension.iter().zip(&self.current_extension).
            take_while(|(lhs, rhs)| lhs == rhs).
            count();

        let shared_extension = &self.current_extension[.. shared_context_len];
        let last_shared_ctx: Element = *shared_extension.last().unwrap();

        let cur_unshared = &self.current_extension[shared_context_len ..];
        let dom_unshared = &dom_extension[shared_context_len ..];

        assert!(
            dom_unshared.len() == args.len(),
            "Need `{}` arguments but `{}` are provided",
            dom_unshared.len(), args.len()
        );

        let last_shared_identity: Element =
            adjoin_op(cwf, CwfRelation::Id, vec![last_shared_ctx]);
        let wkn_shared_to_cur =
            cur_unshared.iter().
            fold(last_shared_identity, |prev, ext| {
                let wkn = adjoin_op(cwf, CwfRelation::Wkn, vec![*ext]);
                adjoin_op(cwf, CwfRelation::Comp, vec![wkn, prev])
            });

        let subst =
            dom_unshared.to_vec().iter(). // TODO: can we get rid of to_vec somehow?
            zip(args.iter()).
            fold(wkn_shared_to_cur, |prev_subst, (next_ext, next_arg)| {
                let required_ty = adjoin_op(cwf, CwfRelation::ExtTy, vec![*next_ext]);
                let required_ty_subst =
                    adjoin_op(cwf, CwfRelation::SubstTy, vec![prev_subst, required_ty]);
                let arg_el = self.add_term(cwf, should_check, &next_arg);
                let arg_ty_el = tm_ty(cwf, arg_el);
                if should_check == EqChecking::Yes {
                    close_cwf(cwf);
                    assert!(
                        els_are_equal(cwf, required_ty_subst, arg_ty_el),
                        "The type of term `{:?}` does not equal the type required",
                        next_arg
                    );
                }
                adjoin_op(
                    cwf,
                    CwfRelation::MorExt, vec![*next_ext, prev_subst, arg_el],
                )
            });

        adjoin_post_compositions(
            cwf,
            *dom_extension.last().unwrap(),
            once(MorphismWithSignature{
                morph: subst,
                dom: *dom_extension.last().unwrap(),
                cod: self.current_ctx(),
            })
        );
        
        subst
    }

    pub fn add_type(&mut self, cwf: &mut Cwf, should_check: EqChecking, ty: &ast::Ty) -> Element {
        match ty {
            ast::Ty::Unit => {
                adjoin_op(cwf, CwfRelation::Unit, vec![self.current_ctx()])
            },
            ast::Ty::Bool => {
                adjoin_op(cwf, CwfRelation::Bool, vec![self.current_ctx()])
            },
            ast::Ty::Eq(lhs, rhs) => {
                let lhs_el = self.add_term(cwf, should_check, lhs);
                let rhs_el = self.add_term(cwf, should_check, rhs);

                let lhs_ty_el = tm_ty(cwf, lhs_el);
                let rhs_ty_el = tm_ty(cwf, rhs_el);

                if should_check == EqChecking::Yes {
                    close_cwf(cwf);

                    assert!(
                        els_are_equal(cwf, lhs_ty_el, rhs_ty_el),
                        "Terms do not have the same type: `{:?}` and `{:?}`", lhs, rhs,
                    );
                }

                adjoin_op(cwf, CwfRelation::Eq, vec![lhs_el, rhs_el])
            },
        }
    }
    pub fn add_term(&mut self, cwf: &mut Cwf, should_check: EqChecking, tm: &ast::Tm) -> Element {
        match tm {
            ast::Tm::Typed{tm, ty} => {
                let ty_el = self.add_type(cwf, should_check, ty);
                let tm_el = self.add_term(cwf, should_check, tm);
                // or the other way round?
                let tm_el_ty = tm_ty(cwf, tm_el);

                if should_check == EqChecking::Yes {
                    close_cwf(cwf);
                    assert!(
                        els_are_equal(cwf, ty_el, tm_el_ty),
                        "Term `{:?}` does not have type `{:?}`", tm, ty
                    );
                }
                tm_el
            },
            ast::Tm::App{fun, args} => {
                let def =
                    self.defs.get(fun).
                    unwrap_or_else(|| panic!("`{}` is undefined", fun));
                let def_extension: Vec<Element> = def.0.clone();
                let def_el: Element = def.1;

                let arg_els: Vec<Element> =
                    args.iter()
                    .map(|arg| self.add_term(cwf, should_check, arg))
                    .collect();

                let subst_el = self.add_substitution(
                    cwf,
                    should_check,
                    &def_extension,
                    args,
                );

                adjoin_op(cwf, CwfRelation::SubstTm, vec![subst_el, def_el])
            },
            ast::Tm::Let{body, result} => {
                let mut self_with_local_defs = self.clone();
                for def in body {
                    self_with_local_defs.add_definition(cwf, should_check, &def);
                }
                let result_el = self_with_local_defs.add_term(cwf, should_check, result);
                result_el
            },
            ast::Tm::UnitTm => {
                adjoin_op(cwf, CwfRelation::UnitTm, vec![self.current_ctx()])
            },
            ast::Tm::True => {
                let true_el = cwf.adjoin_element(CwfSort::Tm);
                cwf.adjoin_rows(CwfRelation::True, once(vec![self.current_ctx(), true_el]));
                true_el
            },
            ast::Tm::False => {
                let false_el = cwf.adjoin_element(CwfSort::Tm);
                cwf.adjoin_rows(CwfRelation::False, once(vec![self.current_ctx(), false_el]));
                false_el
            },
            ast::Tm::Neg(arg) => {
                let arg_el = self.add_term(cwf, should_check, arg);
                let arg_ty_el = tm_ty(cwf, arg_el);
                let bool_el = adjoin_op(cwf, CwfRelation::Bool, vec![self.current_ctx()]);
                if should_check == EqChecking::Yes {
                    close_cwf(cwf);
                    assert!(
                        els_are_equal(cwf, arg_ty_el, bool_el),
                        "{:?} must be of type bool", arg,
                    );
                }
                adjoin_op(cwf, CwfRelation::Neg, vec![arg_el])
            },
            ast::Tm::Refl(arg) => {
                let arg_el = self.add_term(cwf, should_check, arg);
                let refl_el = cwf.adjoin_element(CwfSort::Tm);
                cwf.adjoin_rows(CwfRelation::Refl, once(vec![arg_el, refl_el]));
                refl_el
            },
            ast::Tm::BoolElim{discriminee, into_var, into_ty, true_case, false_case} => {
                // let discriminee_el = self.add_term(cwf, should_check, discriminee);
                // let discriminee_ty_el = tm_ty(cwf, discriminee_el);
                // let bool_el = adjoin_op(cwf, CwfRelation::Bool, vec![self.current_ctx()]);
                // if should_check == EqChecking::Yes {
                //     close_cwf(cwf);
                //     assert!(
                //         els_are_equal(cwf, discriminee_ty_el, bool_el),
                //         "Discriminee {:?} must have type Bool", discriminee
                //     );
                // }

                let (into_ty_el, into_ty_extension) = self.clone().with_args(
                    cwf, should_check, &[(into_var.clone(), ast::Ty::Bool)],
                    |mut extended_self, cwf, should_check| {
                        let into_ty_el = extended_self.add_type(cwf, should_check, into_ty);
                        (into_ty_el, extended_self.current_extension)
                    });

                let true_case_el = self.add_term(cwf, should_check, true_case);
                let false_case_el = self.add_term(cwf, should_check, false_case);

                let true_case_ty_el = tm_ty(cwf, true_case_el);
                let false_case_ty_el = tm_ty(cwf, false_case_el);

                let id_el = adjoin_op(cwf, CwfRelation::Id, vec![self.current_ctx()]);

                let true_el = adjoin_op(cwf, CwfRelation::True, vec![self.current_ctx()]);
                let false_el = adjoin_op(cwf, CwfRelation::False, vec![self.current_ctx()]);

                let subst_true_el = self.add_substitution(
                    cwf,
                    should_check,
                    &into_ty_extension,
                    &[ast::Tm::True],
                );
                let subst_false_el = self.add_substitution(
                    cwf,
                    should_check,
                    &into_ty_extension,
                    &[ast::Tm::False],
                );

                let into_ty_true_el = adjoin_op(cwf, CwfRelation::SubstTy, vec![subst_true_el, into_ty_el]);
                let into_ty_false_el = adjoin_op(cwf, CwfRelation::SubstTy, vec![subst_false_el, into_ty_el]);

                if should_check == EqChecking::Yes {
                    close_cwf(cwf);

                    assert!(
                        els_are_equal(cwf, true_case_ty_el, into_ty_true_el),
                        "Term {:?} does not have type {:?}[{:?} := {:?}]", true_case, into_ty, into_var, "True"
                    );
                    assert!(
                        els_are_equal(cwf, false_case_ty_el, into_ty_false_el),
                        "Term {:?} does not have type {:?}[{:?} := {:?}]", false_case, into_ty, into_var, "False"
                    );
                }

                let elim_el = adjoin_op(cwf, CwfRelation::BoolElim, vec![into_ty_el, true_case_el, false_case_el]);
                let subst_discriminee_el = self.add_substitution(
                    cwf,
                    should_check,
                    &into_ty_extension,
                    &[*discriminee.clone()],
                );

                adjoin_op(cwf, CwfRelation::SubstTm, vec![subst_discriminee_el, elim_el])
            },
        }
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
        let mut cwf = Cwf::new(CwfSignature::new());
        let mut env = Environment::new(&mut cwf);
        for def in &unit {
            env.add_definition(&mut cwf, EqChecking::Yes, &def)
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
