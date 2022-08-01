use crate::ast;
use cwf_theory::cwf::*;
use itertools::Itertools;
use std::collections::{BTreeSet, HashMap};
use std::fmt::Display;
use std::iter::once;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Checking {
    Yes,
    No,
}

#[derive(Clone, Debug)]
struct Definition {
    base_context: Ctx,
    extensions: Vec<(Ty, Ctx)>,
    term: Tm,
}

#[derive(Clone, Debug)]
pub struct Scope {
    definitions: HashMap<String, Definition>,
    empty_context: Ctx,
    extensions: Vec<(Ty, Ctx)>,
    cwf: Cwf,

    context_names: Vec<(Ctx, String)>,
    type_names: Vec<(Ty, String)>,
    term_names: Vec<(Tm, String)>,
}

impl Scope {
    pub fn new() -> Self {
        let mut cwf = Cwf::new();
        let empty_context = cwf.new_ctx();
        cwf.insert_active_ctx(ActiveCtx(empty_context));
        Scope {
            definitions: HashMap::new(),
            empty_context,
            extensions: Vec::new(),
            cwf,
            context_names: Vec::new(),
            type_names: Vec::new(),
            term_names: Vec::new(),
        }
    }
}

//struct MorphismNormalForm {
//    extensions: Vec<(Ctx, Ty, Tm)>,
//    weakenings: Vec<(Ctx, Ty)>,
//    abnormal_base_morphism: Option<Mor>,
//}

impl Scope {
    #[allow(dead_code)]
    fn display_context(&mut self, mut ctx: Ctx) -> impl Display {
        let Self {
            cwf, context_names, ..
        } = self;
        ctx = cwf.ctx_root(ctx);
        once(&format!("{ctx}"))
            .chain(
                context_names
                    .iter()
                    .filter_map(|(c, name)| {
                        if cwf.ctx_root(*c) == ctx {
                            Some(name)
                        } else {
                            None
                        }
                    })
                    .collect::<BTreeSet<&String>>(),
            )
            .join("_")
    }

    #[allow(dead_code)]
    fn display_type(&mut self, mut ty: Ty) -> impl Display {
        let Self {
            cwf, type_names, ..
        } = self;
        ty = cwf.ty_root(ty);
        once(&format!("{ty}"))
            .chain(
                type_names
                    .iter()
                    .filter_map(|(t, name)| {
                        if cwf.ty_root(*t) == ty {
                            Some(name)
                        } else {
                            None
                        }
                    })
                    .collect::<BTreeSet<&String>>(),
            )
            .join("_")
    }

    #[allow(dead_code)]
    fn display_term(&mut self, mut tm: Tm) -> impl Display {
        let Self {
            cwf, term_names, ..
        } = self;
        tm = cwf.tm_root(tm);
        once(&format!("{tm}"))
            .chain(
                term_names
                    .iter()
                    .filter_map(|(t, name)| {
                        if cwf.tm_root(*t) == tm {
                            Some(name)
                        } else {
                            None
                        }
                    })
                    .collect::<BTreeSet<&String>>(),
            )
            .join("_")
    }

    //fn morphism_normal_form(&self, mut mor: Mor) -> MorphismNormalForm {
    //    let mut extensions: Vec<(Ctx, Ty, Tm)> = Vec::new();

    //    while let Some((ctx, ty, mor0, tm)) = self.cwf.mor_ext_pre(mor).next() {
    //        extensions.push((ctx, ty, tm));
    //        mor = mor0;
    //    }
    //    extensions.reverse();

    //    let mut weakenings: Vec<(Ctx, Ty)> = Vec::new();
    //    while let Some((ctx, ty, mor0)) = self.cwf.comp_wkn_pre(mor).next() {
    //        weakenings.push((ctx, ty));
    //        mor = mor0;
    //    }
    //    weakenings.reverse();

    //    let abnormal_base_morphism = match self.cwf.id_pre(mor).next() {
    //        Some(_) => None,
    //        None => Some(mor),
    //    };

    //    MorphismNormalForm {
    //        extensions,
    //        weakenings,
    //        abnormal_base_morphism,
    //    }
    //}

    #[allow(dead_code)]
    fn display_morphism(&mut self, mor: Mor) -> impl Display {
        let dom = self.display_context(self.cwf.dom(mor).next().unwrap());
        let cod = self.display_context(self.cwf.cod(mor).next().unwrap());
        format!("{mor} : {dom} -> {cod}")

        //let signature = format!("{mor} : {dom} -> {cod}");

        //let MorphismNormalForm {
        //    extensions,
        //    weakenings,
        //    abnormal_base_morphism,
        //} = self.morphism_normal_form(mor);
        //let mut ext_str = "".to_string();
        //for (base_ctx, ty, tm) in extensions.iter().copied() {
        //    let var = self.cwf.var(base_ctx, ty).next().unwrap();
        //    let var_displ = self.display_term(var);
        //    let tm_displ = self.display_term(tm);
        //    ext_str.push_str(&format!("  {var_displ} |-> {tm_displ}\n"));
        //}
        //let abnormal_base_str = match abnormal_base_morphism {
        //    None => "".to_string(),
        //    Some(base_mor) => {
        //        let base_dom = self.display_context(self.cwf.dom(base_mor).next().unwrap());
        //        let base_cod = self.display_context(self.cwf.cod(base_mor).next().unwrap());
        //        let weakenings_displ = weakenings.iter().format_with("", |(base_ctx, _), f| {
        //            let base_ctx_displ = self.display_context(*base_ctx);
        //            f(&format_args!("{base_ctx_displ} ->"))
        //        });
        //        formatdoc! {"
        //            Abnormal base
        //            Weakenings:
        //            {weakenings_displ}
        //            base:
        //            {base_mor} : {base_dom} -> {base_cod}
        //        "}
        //    }
        //};
        //formatdoc! {"
        //    {signature}
        //    {ext_str}
        //    {abnormal_base_str}
        //"}
    }

    fn current_context(&self) -> Ctx {
        self.extensions
            .last()
            .map(|(_, ctx)| *ctx)
            .unwrap_or(self.empty_context)
    }

    fn add_weakening_from_base(&mut self, def: &Definition) -> Mor {
        let base_to_current_exts: &[(Ty, Ctx)] =
            match self.extensions.iter().position(|(_, ctx)| {
                // TODO: Need to check the *roots* here, not elements themselves.
                *ctx == def.base_context
            }) {
                None => {
                    debug_assert_eq!(
                        self.cwf.ctx_root(self.empty_context),
                        self.cwf.ctx_root(def.base_context)
                    );
                    self.extensions.as_slice()
                }
                Some(i) => &self.extensions[(i + 1)..],
            };

        let mut w = self.cwf.define_id(def.base_context);
        for (_, ext_ctx) in base_to_current_exts.iter().copied() {
            let wkn = self.cwf.define_ext_wkn(ext_ctx);
            w = self.cwf.define_comp(wkn, w);
        }
        w
    }

    fn add_substitution(&mut self, checking: Checking, def: &Definition, args: &[Tm]) -> Mor {
        if checking == Checking::Yes {
            assert_eq!(args.len(), def.extensions.len())
        }
        let mut subst = self.add_weakening_from_base(def);
        for (arg, (ty, ext_ctx)) in args.iter().copied().zip(def.extensions.iter().copied()) {
            let subst_ty = self.cwf.define_subst_ty(subst, ty);
            if checking == Checking::Yes {
                let arg_ty = self.cwf.define_tm_ty(arg);
                self.cwf.close();
                assert_eq!(self.cwf.ty_root(subst_ty), self.cwf.ty_root(arg_ty));
            } else {
                self.cwf.insert_tm_ty(TmTy(arg, subst_ty));
            }
            subst = self.cwf.define_ext_mor(ext_ctx, subst, arg);
        }
        subst
    }

    fn add_type(&mut self, checking: Checking, ty: &ast::Ty) -> Ty {
        match ty {
            ast::Ty::Unit => {
                let ty = self.cwf.define_unit(self.current_context());
                self.type_names.push((ty, "Unit".to_string()));
                ty
            }
            ast::Ty::Bool => {
                let ty = self.cwf.define_bool(self.current_context());
                self.type_names.push((ty, "Bool".to_string()));
                ty
            }
            ast::Ty::Eq(lhs, rhs) => {
                let lhs = self.add_term(checking, lhs);
                let rhs = self.add_term(checking, rhs);

                if checking == Checking::Yes {
                    let lhs_ty = self.cwf.define_tm_ty(lhs);
                    let rhs_ty = self.cwf.define_tm_ty(lhs);
                    self.cwf.close();
                    assert_eq!(self.cwf.ty_root(lhs_ty), self.cwf.ty_root(rhs_ty));
                }
                let ty = self.cwf.define_eq(lhs, rhs);
                let lhs_displ = self.display_term(lhs);
                let rhs_displ = self.display_term(rhs);
                self.type_names
                    .push((ty, format!("Eq({lhs_displ}, {rhs_displ})")));
                ty
            }
            ast::Ty::Nat => todo!(),
        }
    }
    fn add_term(&mut self, checking: Checking, tm: &ast::Tm) -> Tm {
        match tm {
            ast::Tm::Variable(name) => {
                let def = self.definitions.get(name).unwrap().clone();
                let wkn = self.add_weakening_from_base(&def);
                let tm = self.cwf.define_subst_tm(wkn, def.term);
                self.term_names.push((tm, name.to_string()));
                tm
            }
            ast::Tm::Typed { tm, ty } => {
                let tm = self.add_term(checking, tm);
                let ty = self.add_type(checking, ty);
                if checking == Checking::Yes {
                    let tm_ty = self.cwf.define_tm_ty(tm);
                    self.cwf.close();
                    assert_eq!(self.cwf.ty_root(tm_ty), self.cwf.ty_root(ty));
                }
                tm
            }
            ast::Tm::App { fun, args } => {
                let def = self.definitions.get(fun).unwrap().clone();
                let args: Vec<Tm> = args
                    .iter()
                    .map(|arg| self.add_term(checking, arg))
                    .collect();
                let subst = self.add_substitution(checking, &def, args.as_slice());
                let tm = self.cwf.define_subst_tm(subst, def.term);
                let args_displ = args
                    .iter()
                    .copied()
                    .format_with(", ", |arg, f| f(&self.display_term(arg)));
                let name = format!("{fun}({args_displ})");
                self.term_names.push((tm, name));
                tm
            }
            ast::Tm::Let { body, result } => {
                let before_defs = self.definitions.clone();
                for def in body {
                    self.add_definition(checking, def);
                }
                let result = self.add_term(checking, result);
                self.definitions = before_defs;
                result
            }
            ast::Tm::UnitTm => {
                let tm = self.cwf.define_unit_tm(self.current_context());
                self.term_names.push((tm, "unit".to_string()));
                tm
            }
            ast::Tm::ElimUnit {
                discriminee,
                var,
                into_ty,
                unit_case,
            } => {
                let discriminee = self.add_term(checking, discriminee);
                let unit_ty = self.cwf.define_unit(self.current_context());

                // Check that `discriminee` has the right type.
                if checking == Checking::Yes {
                    let tm_ty = self.cwf.define_tm_ty(discriminee);
                    self.cwf.close();
                    assert_eq!(self.cwf.ty_root(unit_ty), self.cwf.ty_root(tm_ty));
                } else {
                    self.cwf.insert_tm_ty(TmTy(discriminee, unit_ty));
                }

                // Check `into_ty`.
                if checking == Checking::Yes {
                    let before_self = self.clone();
                    self.adjoin_variable(Checking::No, var, &ast::Ty::Unit);
                    self.add_type(Checking::Yes, into_ty);
                    *self = before_self;
                }

                // Adjoin `into_ty`, back off into current context again. We remember the extended
                // context and the unit type.
                self.extend_context(Checking::No, var, &ast::Ty::Unit);
                let into_ty = self.add_type(Checking::No, into_ty);
                let (_, ext_ctx) = self.extensions.pop().unwrap();
                self.definitions.remove(var).unwrap();

                // Add `unit_case`.
                let unit_case = self.add_term(checking, unit_case);

                // Adjoin morphism `subst_unit = [var |-> unit]`.
                let id = self.cwf.define_id(self.current_context());
                let unit_tm = self.cwf.define_unit_tm(self.current_context());
                let subst_unit = self.cwf.define_ext_mor(ext_ctx, id, unit_tm);

                // Substitute `into_ty` into current context.
                let into_ty_unit_subst = self.cwf.define_subst_ty(subst_unit, into_ty);

                if checking == Checking::Yes {
                    let unit_case_ty = self.cwf.define_tm_ty(unit_case);
                    self.cwf.close();
                    assert_eq!(
                        self.cwf.ty_root(unit_case_ty),
                        self.cwf.ty_root(into_ty_unit_subst)
                    );
                } else {
                    self.cwf.insert_tm_ty(TmTy(unit_case, into_ty_unit_subst));
                }

                let unit_ind = self.cwf.define_unit_ind(into_ty, unit_case);

                // Adjoin morphism `subst_discriminee = [var |-> discriminee]`.
                let subst_discriminee = self.cwf.define_ext_mor(ext_ctx, id, discriminee);

                // Substitute `unit_ind` into current context along `subst_discriminee`.
                let elim_tm = self.cwf.define_subst_tm(subst_discriminee, unit_ind);
                self.term_names.push((elim_tm, "elim_unit".to_string()));
                elim_tm
            }
            ast::Tm::False => {
                let tm = self.cwf.define_false_tm(self.current_context());
                self.term_names.push((tm, "false".to_string()));
                tm
            }
            ast::Tm::True => {
                let tm = self.cwf.define_true_tm(self.current_context());
                self.term_names.push((tm, "true".to_string()));
                tm
            }
            ast::Tm::ElimBool {
                discriminee,
                var,
                into_ty,
                false_case,
                true_case,
            } => {
                let discriminee = self.add_term(checking, discriminee);
                let bool_ty = self.cwf.define_bool(self.current_context());

                // Check that `discriminee` has the right type.
                if checking == Checking::Yes {
                    let tm_ty = self.cwf.define_tm_ty(discriminee);
                    self.cwf.close();
                    assert_eq!(self.cwf.ty_root(bool_ty), self.cwf.ty_root(tm_ty));
                } else {
                    self.cwf.insert_tm_ty(TmTy(discriminee, bool_ty));
                }

                if checking == Checking::Yes {
                    // Check `into_ty`.
                    let before_self = self.clone();
                    self.adjoin_variable(Checking::No, var, &ast::Ty::Bool);
                    self.add_type(Checking::Yes, into_ty);
                    *self = before_self;
                }

                // Adjoin `into_ty`, back off into current context again.
                self.extend_context(Checking::No, var, &ast::Ty::Bool);
                let into_ty = self.add_type(Checking::No, into_ty);
                let (_, ext_ctx) = self.extensions.pop().unwrap();
                self.definitions.remove(var).unwrap();

                // Add `true_case` and `false_case` terms.
                let false_case = self.add_term(checking, false_case);
                let true_case = self.add_term(checking, true_case);

                // Adjoin morphisms `subst_false = [var |-> false]` and
                // `subst_true = [var |-> true]`.
                let id = self.cwf.define_id(self.current_context());
                let false_tm = self.cwf.define_false_tm(self.current_context());
                let true_tm = self.cwf.define_true_tm(self.current_context());
                let subst_false = self.cwf.define_ext_mor(ext_ctx, id, false_tm);
                let subst_true = self.cwf.define_ext_mor(ext_ctx, id, true_tm);

                // Substitute `into_ty` into current context, once with `true` and once with
                // `false`.
                let into_ty_false_subst = self.cwf.define_subst_ty(subst_false, into_ty);
                let into_ty_true_subst = self.cwf.define_subst_ty(subst_true, into_ty);

                if checking == Checking::Yes {
                    let false_case_ty = self.cwf.define_tm_ty(false_case);
                    let true_case_ty = self.cwf.define_tm_ty(true_case);
                    self.cwf.close();
                    assert_eq!(
                        self.cwf.ty_root(false_case_ty),
                        self.cwf.ty_root(into_ty_false_subst)
                    );
                    assert_eq!(
                        self.cwf.ty_root(true_case_ty),
                        self.cwf.ty_root(into_ty_true_subst)
                    );
                } else {
                    self.cwf.insert_tm_ty(TmTy(false_case, into_ty_false_subst));
                    self.cwf.insert_tm_ty(TmTy(true_case, into_ty_true_subst));
                }

                let bool_ind = self.cwf.define_bool_ind(into_ty, false_case, true_case);

                // Adjoin morphism `subst_discriminee = [var |-> discriminee]`.
                let subst_discriminee = self.cwf.define_ext_mor(ext_ctx, id, discriminee);

                // Substitute `bool_ind` into current context along `subst_discriminee`.
                let elim_tm = self.cwf.define_subst_tm(subst_discriminee, bool_ind);
                self.term_names.push((elim_tm, "elim_bool".to_string()));
                elim_tm
            }
            ast::Tm::Refl(s) => {
                let s = self.add_term(checking, s);
                let tm = self.cwf.define_refl(s);
                let s_displ = self.display_term(s);
                self.term_names.push((tm, format!("refl({s_displ})")));
                tm
            }
            ast::Tm::Zero => todo!(),
            ast::Tm::Succ(_) => todo!(),
            ast::Tm::ElimNat { .. } => todo!(),
        }
    }
    // Adjoing indeterminate term of a given type, do not change context.
    fn adjoin_variable(&mut self, checking: Checking, name: &str, ty: &ast::Ty) {
        let ty = self.add_type(checking, ty);
        let var = self.cwf.new_tm();
        self.cwf.insert_tm_ty(TmTy(var, ty));
        self.definitions.insert(
            name.to_string(),
            Definition {
                base_context: self.current_context(),
                extensions: Vec::new(),
                term: var,
            },
        );
        self.term_names.push((var, name.to_string()));
    }
    // Extend context by a variable.
    fn extend_context(&mut self, checking: Checking, name: &str, ty: &ast::Ty) {
        let ty = self.add_type(checking, ty);
        let base_ctx = self.current_context();
        let ext_ctx = self.cwf.new_ctx();
        self.cwf.insert_base_ctx(BaseCtx(ext_ctx, base_ctx));
        self.cwf.insert_ext_ty(ExtTy(ext_ctx, ty));

        let var = self.cwf.define_ext_var(ext_ctx);
        self.extensions.push((ty, ext_ctx));
        self.definitions.insert(
            name.to_string(),
            Definition {
                base_context: ext_ctx,
                extensions: Vec::new(),
                term: var,
            },
        );
        self.term_names.push((var, name.to_string()));
        let base_ctx_name = self.display_context(base_ctx);
        self.context_names
            .push((ext_ctx, format!("{base_ctx_name}.{name}")));
    }

    pub fn add_definition(&mut self, checking: Checking, def: &ast::Def) {
        use ast::Def::*;
        match def {
            Dump { message } => {
                if checking == Checking::Yes {
                    self.cwf.close();
                    if let Some(message) = message {
                        println!("{}", message);
                    }
                    println!("{}", self.cwf);
                    println!("{}", (0..80).map(|_| "─").collect::<String>());
                }
            }
            Def { name, args, ty, tm } if args.is_empty() => {
                let tm = self.add_term(checking, tm);
                let ty = self.add_type(checking, ty);
                if checking == Checking::Yes {
                    let tm_ty = self.cwf.define_tm_ty(tm);
                    self.cwf.close();
                    assert_eq!(self.cwf.ty_root(ty), self.cwf.ty_root(tm_ty));
                } else {
                    self.cwf.insert_tm_ty(TmTy(tm, ty));
                }
                self.definitions.insert(
                    name.to_string(),
                    Definition {
                        base_context: self.current_context(),
                        extensions: Vec::new(),
                        term: tm,
                    },
                );
            }
            Def { name, args, ty, tm } => {
                if checking == Checking::Yes {
                    let before_self = self.clone();
                    for (arg_name, arg_ty) in args {
                        self.adjoin_variable(Checking::Yes, arg_name, arg_ty);
                    }
                    let tm = self.add_term(Checking::Yes, tm);
                    self.term_names.push((tm, name.clone()));
                    let ty = self.add_type(Checking::Yes, ty);
                    let tm_ty = self.cwf.define_tm_ty(tm);
                    self.cwf.close();
                    assert_eq!(self.cwf.ty_root(tm_ty), self.cwf.ty_root(ty));
                    *self = before_self;
                }

                let before_definitions = self.definitions.clone();
                let before_extensions = self.extensions.clone();

                let mut extensions = Vec::new();
                for (arg_name, arg_ty) in args {
                    self.extend_context(Checking::No, arg_name, arg_ty);
                    extensions.push(*self.extensions.last().unwrap())
                }
                let tm = self.add_term(Checking::No, tm);
                let ty = self.add_type(Checking::No, ty);
                self.cwf.insert_tm_ty(TmTy(tm, ty));

                self.definitions = before_definitions;
                self.extensions = before_extensions;

                self.definitions.insert(
                    name.to_string(),
                    Definition {
                        base_context: self.current_context(),
                        extensions,
                        term: tm,
                    },
                );
                self.term_names.push((tm, format!("{name}_def")));
            }
        }
    }
}
