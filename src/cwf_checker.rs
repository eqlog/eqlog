use eqlog::element::*;
use crate::cwf::*;
use std::collections::HashMap;
use std::iter::once;
use crate::lang::ast;

#[derive(Clone, Debug, PartialEq, Eq)]
struct Extension {
    ty: Element,
    ext_ctx: Element,
    wkn: Element,
    var: Element,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Environment {
    defs: HashMap<String, (Vec<Extension>, Element)>,
    empty_ctx: Element,
    current_extension: Vec<Extension>,
}

impl Environment {
    fn new(cwf: &mut Cwf) -> Self {
        Environment {
            defs: HashMap::new(),
            empty_ctx: cwf.adjoin_element(CwfSort::Ctx),
            current_extension: vec![],
        }
    }
    fn current_ctx(&self) -> Element {
        self.current_extension.last().map(|ext| ext.ext_ctx).unwrap_or(self.empty_ctx)
    }
    fn add_definition(&mut self, cwf: &mut Cwf, def: &ast::Def) {
        let mut self_ = self.clone();
        for (arg_name, arg_ty) in &def.args {
            self_.extend_ctx(cwf, arg_name.clone(), arg_ty);
        }
        let def_el = self_.add_term(cwf, &def.tm);
        self.defs.insert(def.name.clone(), (self_.current_extension, def_el));
    }
    fn extend_ctx(&mut self, cwf: &mut Cwf, var_name: String, ty: &ast::Ty) {
        let ty_el = self.add_type(cwf, ty);
        let ext_ctx_el = cwf.adjoin_element(CwfSort::Ctx);
        cwf.adjoin_rows(
            CwfRelation::ExtCtx,
            once(vec![self.current_ctx(), ty_el, ext_ctx_el]),
        );
        let wkn_el = adjoin_op(cwf, CwfRelation::Wkn, vec![ext_ctx_el]);
        let var_el = adjoin_op(cwf, CwfRelation::Var, vec![ext_ctx_el]);

        self.current_extension.push(Extension{
            ty: ty_el,
            ext_ctx: ext_ctx_el,
            wkn: wkn_el,
            var: var_el,
        });
        self.defs.insert(var_name, (self.current_extension.clone(), var_el));
    }
    fn add_type(&mut self, cwf: &mut Cwf, ty: &ast::Ty) -> Element {
        match ty {
            ast::Ty::Bool => {
                let bool_el = cwf.adjoin_element(CwfSort::Ty);
                cwf.adjoin_rows(CwfRelation::Bool, once(vec![self.current_ctx(), bool_el]));
                close_cwf(cwf);
                bool_el
            },
            ast::Ty::Eq(lhs, rhs) => {
                let lhs_el = self.add_term(cwf, lhs);
                let rhs_el = self.add_term(cwf, rhs);

                let lhs_ty_el = tm_ty(cwf, lhs_el);
                let rhs_ty_el = tm_ty(cwf, rhs_el);

                close_cwf(cwf);

                assert!(
                    els_are_equal(cwf, lhs_ty_el, rhs_ty_el),
                    "Terms do not have the same type: `{:?}` and `{:?}`", lhs, rhs,
                );

                adjoin_op(cwf, CwfRelation::Eq, vec![lhs_el, rhs_el])
            },
        }
    }
    fn add_term(&mut self, cwf: &mut Cwf, tm: &ast::Tm) -> Element {
        match tm {
            ast::Tm::Typed{tm, ty} => {
                let ty_el = self.add_type(cwf, ty);
                let tm_el = self.add_term(cwf, tm);
                // or the other way round?
                let tm_el_ty = tm_ty(cwf, tm_el);
                close_cwf(cwf);
                assert!(
                    els_are_equal(cwf, ty_el, tm_el_ty),
                    "Term `{:?}` does not have type `{:?}`", tm, ty
                );
                tm_el
            },
            ast::Tm::App{fun, args} => {
                let def =
                    self.defs.get(fun).
                    unwrap_or_else(|| panic!("`{}` is undefined", fun));
                let def_exts = &def.0;
                let def_el = def.1;

                let shared_context_len: usize =
                    def_exts.iter().zip(&self.current_extension).
                    take_while(|(lhs, rhs)| lhs == rhs).
                    count();
                let last_shared_ctx: Element =
                    self.current_extension[.. shared_context_len].first().
                    map(|extension| extension.ext_ctx).
                    unwrap_or(self.empty_ctx);
                let last_shared_identity: Element =
                    adjoin_op(cwf, CwfRelation::Id, vec![last_shared_ctx]);

                let cur_unshared = &self.current_extension[shared_context_len ..];
                let def_unshared = &def_exts[shared_context_len ..];
                assert_eq!(
                    def_unshared.len(), args.len(),
                    "Function `{}` takes `{}` arguments, `{}` were provided",
                    fun, def_unshared.len(), args.len()
                );
                let wkn_shared_to_cur =
                    cur_unshared.iter().
                    fold(last_shared_identity, |prev, ext| {
                        adjoin_op(cwf, CwfRelation::Comp, vec![ext.wkn, prev])
                    });

                let subst_def_to_current =
                    def_unshared.to_vec().iter(). // TODO: can we get rid of to_vec somehow?
                    zip(args).
                    fold(wkn_shared_to_cur, |prev_subst, (next_ext, next_arg)| {
                        let next_ty_subst =
                            adjoin_op(cwf, CwfRelation::SubstTy, vec![prev_subst, next_ext.ty]);
                        let mut arg_el = self.add_term(cwf, next_arg);
                        close_cwf(cwf);
                        arg_el = cwf.representative(arg_el);
                        let arg_ty = tm_ty(cwf, arg_el);
                        close_cwf(cwf);
                        assert!(
                            els_are_equal(cwf, next_ty_subst, arg_ty),
                            "The type of term `{:?}` does not equal the type required by `{}`",
                            next_arg, fun,
                        );
                        adjoin_op(
                            cwf,
                            CwfRelation::MorExt, vec![next_ext.ext_ctx, prev_subst, arg_el],
                        )
                    });

                adjoin_op(cwf, CwfRelation::SubstTm, vec![subst_def_to_current, def_el])
            },
            ast::Tm::Let{body, result} => {
                let mut self_ = self.clone();
                for def in body {
                    self_.add_definition(cwf, def);
                }
                let result_el = self_.add_term(cwf, result);
                result_el
            },
            ast::Tm::True => {
                let true_el = cwf.adjoin_element(CwfSort::Tm);
                cwf.adjoin_rows(CwfRelation::True, once(vec![self.current_ctx(), true_el]));
                close_cwf(cwf);
                true_el
            },
            ast::Tm::False => {
                let false_el = cwf.adjoin_element(CwfSort::Tm);
                cwf.adjoin_rows(CwfRelation::False, once(vec![self.current_ctx(), false_el]));
                close_cwf(cwf);
                false_el
            },
            ast::Tm::Neg(arg) => {
                let arg_el = self.add_term(cwf, arg);
                let neg_el = cwf.adjoin_element(CwfSort::Tm);
                cwf.adjoin_rows(CwfRelation::Neg, once(vec![arg_el, neg_el]));
                close_cwf(cwf);
                neg_el
            },
            ast::Tm::Refl(arg) => {
                let arg_el = self.add_term(cwf, arg);
                let refl_el = cwf.adjoin_element(CwfSort::Tm);
                cwf.adjoin_rows(CwfRelation::Refl, once(vec![arg_el, refl_el]));
                close_cwf(cwf);
                refl_el
            },
            ast::Tm::BoolElim{discriminee, into_var, into_ty, true_case, false_case} => {
                let discriminee_el = self.add_term(cwf, discriminee);
                let mut discriminee_ty_el =
                    cwf.rows(CwfRelation::TmTy).filter(|r| r[0] == discriminee_el).map(|r| r[1]).next().
                    unwrap_or_else(|| panic!("Term `{:?}` has unknown type", discriminee));

                let mut bool_el = self.add_type(cwf, &ast::Ty::Bool);
                discriminee_ty_el = cwf.representative(discriminee_ty_el);
                bool_el = cwf.representative(bool_el);
                assert_eq!(
                    discriminee_ty_el, bool_el,
                    "Discriminee {:?} must have type Bool", discriminee
                );

                let mut self_ = self.clone();
                self_.extend_ctx(cwf, into_var.clone(), &ast::Ty::Bool);
                let Extension{ty, ext_ctx, wkn, var} = *self_.current_extension.last().unwrap();
                let into_ty_el = self_.add_type(cwf, into_ty);

                let mut true_case_el = self.add_term(cwf, true_case);
                let mut false_case_el = self.add_term(cwf, false_case);

                let id_el = cwf.adjoin_element(CwfSort::Mor);
                cwf.adjoin_rows(CwfRelation::Id, once(vec![self.current_ctx(), id_el]));

                let true_el = cwf.adjoin_element(CwfSort::Tm);
                cwf.adjoin_rows(CwfRelation::True, once(vec![self.current_ctx(), true_el]));
                let false_el = cwf.adjoin_element(CwfSort::Tm);
                cwf.adjoin_rows(CwfRelation::False, once(vec![self.current_ctx(), false_el]));

                let subst_true_el = cwf.adjoin_element(CwfSort::Mor);
                let subst_false_el = cwf.adjoin_element(CwfSort::Mor);

                cwf.adjoin_rows(CwfRelation::MorExt, vec![
                    vec![ext_ctx, id_el, true_el, subst_true_el],
                    vec![ext_ctx, id_el, false_el, subst_false_el],
                ]);

                let mut into_ty_true_el = cwf.adjoin_element(CwfSort::Ty);
                let mut into_ty_false_el = cwf.adjoin_element(CwfSort::Ty);

                cwf.adjoin_rows(CwfRelation::SubstTy, vec![
                    vec![subst_true_el, into_ty_el, into_ty_true_el],
                    vec![subst_false_el, into_ty_el, into_ty_false_el],
                ]);

                close_cwf(cwf);

                true_case_el = cwf.representative(true_case_el);
                false_case_el = cwf.representative(false_case_el);

                into_ty_true_el = cwf.representative(into_ty_true_el);
                into_ty_false_el = cwf.representative(into_ty_false_el);

                let true_case_ty_el =
                    cwf.rows(CwfRelation::TmTy).filter(|r| r[0] == true_case_el).map(|r| r[1]).next().
                    unwrap_or_else(|| panic!("Term `{:?}` has unknown type", true_case));
                let false_case_ty_el =
                    cwf.rows(CwfRelation::TmTy).filter(|r| r[0] == false_case_el).map(|r| r[1]).next().
                    unwrap_or_else(|| panic!("Term `{:?}` has unknown type", false_case));

                assert!(
                    true_case_ty_el == into_ty_true_el,
                    "Term {:?} does not have type {:?}[{:?} := {:?}]", true_case, into_ty, into_var, "True"
                );
                assert!(
                    false_case_ty_el == into_ty_false_el,
                    "Term {:?} does not have type {:?}[{:?} := {:?}]", false_case, into_ty, into_var, "False"
                );

                let elim_el = cwf.adjoin_element(CwfSort::Tm);
                cwf.adjoin_rows(CwfRelation::BoolElim, once(vec![into_ty_el, true_case_el, false_case_el, elim_el]));

                let subst_discriminee_el = cwf.adjoin_element(CwfSort::Mor);
                cwf.adjoin_rows(CwfRelation::MorExt, vec![
                    vec![ext_ctx, id_el, discriminee_el, subst_discriminee_el],
                ]);

                let result_el = cwf.adjoin_element(CwfSort::Tm);
                cwf.adjoin_rows(CwfRelation::SubstTm, once(vec![subst_discriminee_el, elim_el, result_el]));

                close_cwf(cwf);

                cwf.representative(result_el)
            },
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use ast::*;

    #[test]
    fn test_bool_identity() {
        let mut cwf = Cwf::new(CwfSignature::new());
        let mut env = Environment::new(&mut cwf);
        env.add_definition(&mut cwf, &ast::Def{
            name: "id".to_string(),
            args: vec![("x".to_string(), Ty::Bool)],
            tm: Tm::App{fun: "x".to_string(), args: vec![]},
        });
    }

    #[test]
    fn test_bool_identity_typed() {
        let mut cwf = Cwf::new(CwfSignature::new());
        let mut env = Environment::new(&mut cwf);
        env.add_definition(&mut cwf, &ast::Def{
            name: "id".to_string(),
            args: vec![("x".to_string(), Ty::Bool)],
            tm: Tm::Typed{
                tm: Box::new(Tm::App{fun: "x".to_string(), args: vec![]}),
                ty: Box::new(Ty::Bool),
            },
        });
    }

    #[test]
    fn test_true_refl() {
        let mut cwf = Cwf::new(CwfSignature::new());
        let mut env = Environment::new(&mut cwf);
        env.add_definition(&mut cwf, &ast::Def{
            name: "r".to_string(),
            args: vec![],
            tm: Tm::Refl(Box::new(Tm::True)),
        });
    }

    #[test]
    fn test_true_refl_typed() {
        let mut cwf = Cwf::new(CwfSignature::new());
        let mut env = Environment::new(&mut cwf);

        // `Refl True`
        env.add_definition(&mut cwf, &ast::Def{
            name: "r".to_string(),
            args: vec![],
            tm: Tm::Typed{
                tm: Box::new(Tm::Refl(Box::new(Tm::True))),
                ty: Box::new(Ty::Eq(Box::new(Tm::True), Box::new(Tm::True))),
            },
        });
    }

    #[test] #[should_panic]
    fn test_refl_ill_typed() {
        let mut cwf = Cwf::new(CwfSignature::new());
        let mut env = Environment::new(&mut cwf);

        // `Refl True`
        env.add_definition(&mut cwf, &ast::Def{
            name: "r".to_string(),
            args: vec![],
            tm: Tm::Typed{
                tm: Box::new(Tm::Refl(Box::new(Tm::True))),
                ty: Box::new(Ty::Eq(Box::new(Tm::True), Box::new(Tm::True))),
            },
        });

        // But this is false: the type of `Refl True` is not `Bool`
        env.add_definition(&mut cwf, &ast::Def{
            name: "r'".to_string(),
            args: vec![],
            tm: Tm::Typed{
                tm: Box::new(Tm::Refl(Box::new(Tm::True))),
                ty: Box::new(Ty::Bool),
            },
        });
    }

    #[test]
    fn test_refl_of_var() {
        let mut cwf = Cwf::new(CwfSignature::new());
        let mut env = Environment::new(&mut cwf);

        let xvar = Box::new(Tm::App{fun: "x".to_string(), args: vec![]});

        env.add_definition(&mut cwf, &ast::Def{
            name: "r".to_string(),
            args: vec![("x".to_string(), Ty::Bool)],
            tm: Tm::Let{
                body: vec![
                    // assert that `x: Bool`
                    Def{
                        name: "_0".to_string(),
                        args: vec![],
                        tm: Tm::Typed{
                            tm: xvar.clone(),
                            ty: Box::new(Ty::Bool),
                        },
                    },
                ],
                result: Box::new(Tm::Typed{
                    tm: Box::new(Tm::Refl(xvar.clone())),
                    ty: Box::new(Ty::Eq(xvar.clone(), xvar.clone())),
                }),
            }
        });
    }

    #[test]
    fn test_subst_of_refl_of_var() {
        let mut cwf = Cwf::new(CwfSignature::new());
        let mut env = Environment::new(&mut cwf);

        let xvar = Box::new(Tm::App{fun: "x".to_string(), args: vec![]});

        // show that True has type Bool
        env.add_definition(&mut cwf, &ast::Def{
            name: "r".to_string(),
            args: vec![("x".to_string(), Ty::Bool)],
            tm: Tm::Let{
                body: vec![
                    // assert that `x: Bool`
                    Def{
                        name: "_0".to_string(),
                        args: vec![],
                        tm: Tm::Typed{
                            tm: xvar.clone(),
                            ty: Box::new(Ty::Bool),
                        },
                    },
                ],
                result: Box::new(Tm::Typed{
                    tm: Box::new(Tm::Refl(xvar.clone())),
                    ty: Box::new(Ty::Eq(xvar.clone(), xvar.clone())),
                }),
            }
        });

        // substitute `True` for `x` in `r`; this should have type `Eq True True`
        env.add_definition(&mut cwf, &ast::Def{
            name: "rtrue".to_string(),
            args: vec![],
            tm: Tm::Typed{
                tm: Box::new(Tm::App{fun: "r".to_string(), args: vec![Tm::True]}),
                ty: Box::new(Ty::Eq(Box::new(Tm::True), Box::new(Tm::True))),
            },
        });
    }

    #[test]
    fn test_neg_of_true() {
        let mut cwf = Cwf::new(CwfSignature::new());
        let mut env = Environment::new(&mut cwf);

        // show that `Neg True: Bool`
        env.add_definition(&mut cwf, &ast::Def{
            name: "negtrue".to_string(),
            args: vec![],
            tm: Tm::Typed{
                tm: Box::new(Tm::Neg(Box::new(Tm::True))),
                ty: Box::new(Ty::Bool),
            },
        });

        let negtrue_tm = Box::new(Tm::App{fun: "negtrue".to_string(), args: vec![]});

        // `refl False: Eq (Neg True) False`
        env.add_definition(&mut cwf, &ast::Def{
            name: "r".to_string(),
            args: vec![],
            tm: Tm::Typed{
                tm: Box::new(Tm::Refl(Box::new(Tm::False))),
                ty: Box::new(Ty::Eq(negtrue_tm, Box::new(Tm::False))),
            },
        });
    }

    #[test]
    fn bool_elim_neg() {
        let mut cwf = Cwf::new(CwfSignature::new());
        let mut env = Environment::new(&mut cwf);

        env.add_definition(&mut cwf, &ast::Def{
            name: "negtrue".to_string(),
            args: vec![],
            tm: Tm::Typed{
                tm: Box::new(Tm::BoolElim{
                    discriminee: Box::new(Tm::True),
                    into_var: "x".to_string(),
                    into_ty: Box::new(Ty::Bool),
                    true_case: Box::new(Tm::False),
                    false_case: Box::new(Tm::True),
                }),
                ty: Box::new(Ty::Bool),
            },
        });

        let negtrue_tm = Box::new(Tm::App{fun: "negtrue".to_string(), args: vec![]});

        // `refl False: Eq (Neg True) False`
        env.add_definition(&mut cwf, &ast::Def{
            name: "r".to_string(),
            args: vec![],
            tm: Tm::Typed{
                tm: Box::new(Tm::Refl(Box::new(Tm::False))),
                ty: Box::new(Ty::Eq(negtrue_tm, Box::new(Tm::False))),
            },
        });
    }
} 
