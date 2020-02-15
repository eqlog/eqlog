use scopeguard::{guard, ScopeGuard};
use super::model::Model;
use super::cwf::*;
use super::lang::ast::*;

pub struct TypeChecker<T: Model> {
    model: T,
    ctxs : Vec<CtxInfo>,
}

struct CtxInfo {
    syntax: Ctx,
    // morphism from previous (if any) context to current
    weakening: Option<Morph>,
    defs: Vec<(String, Tm, Ty)>,
}

impl<TModel: Model> TypeChecker<TModel> {
    pub fn new(mut model: TModel) -> TypeChecker<TModel> {
        let empty = model.empty_ctx();
        TypeChecker {
            model: model,
            ctxs: vec![CtxInfo {
                syntax: empty,
                weakening: None,
                defs: vec![]
            }],
        }
    }

    // Saves the current number of context extensions and definitions
    // in the current context and returns a scopeguard that will restore
    // to this state when it is dropped. The scope guard takes ownership
    // of the TC.
    fn save_ctx<'a>(&'a mut self) ->
            ScopeGuard<&mut TypeChecker<TModel>, impl FnOnce(&'a mut TypeChecker<TModel>)>
    {
        let depth = self.ctxs.len();
        assert!(depth > 0); // always have empty context
        let num_defs = self.ctxs.last().unwrap().defs.len();
        guard(self, move |s| {
            s.ctxs.truncate(depth);
            s.ctxs.last_mut().unwrap().defs.truncate(num_defs)
        })
    }

    fn extend(&mut self, ext: &CtxExt) -> Result<Ty, String> {
        let ty = self.check_ty(&ext.1)?;
        let new_ctx = self.model.comprehension(&ty);
        let weakening = self.model.weakening(&ty);
        let mut defs = vec![];

        if let Some(ref name) = ext.0 {
            let var_ty = Self::subst_ty(&mut self.model, &weakening, &ty);
            defs.push((name.clone(), self.model.var(&ty), var_ty))
        }
        
        let new_ctx_info = CtxInfo {
            syntax: new_ctx,
            weakening: Some(weakening),
            defs: defs
        };

        self.ctxs.push(new_ctx_info);
        Ok(ty)
    }

    pub fn check_def(&mut self, def: &Def) -> Result<Tm, String> {
        let mut s = self.save_ctx();
        for ext in def.ctx.iter() {
            s.extend(ext)?;
        }
        let ret_ty = s.check_ty(&def.ret_ty)?;
        s.check_tm_ty(&def.body, &ret_ty)
    }

    fn check_let<T, F>(
        &mut self, check_body: F,
        name: &DefId, ty: &Expr, val: &Expr, body: &Expr) -> Result<T, String>
            where F : FnOnce(&mut Self, &Expr) -> Result<T, String>
    {
        let mut s = self.save_ctx();
        let ty = s.check_ty(ty)?;
        let val = s.check_tm_ty(val, &ty)?;
        if let Some(name) = name {
            s.ctxs.last_mut().unwrap().defs.push((name.clone(), val, ty));
        };
        check_body(&mut s, body)
    }

    pub fn check_ty(&mut self, expr: &Expr) -> Result<Ty, String> {
        let cur_ctx_syn = &self.ctxs.last().unwrap().syntax;
        match expr {
            Expr::App(id, v) =>
                match (id.as_str(), &v[..]) {
                    ("bool", []) => Ok(self.model.bool_ty(cur_ctx_syn)),
                    ("eq", [a, b]) => self.check_eq(a, b),
                    (s, v) => Err(format!("Unexpected {} with {} args", s, v.len()))
                },
            Expr::Let { name, ty, val, body } =>
                self.check_let(|s, body| s.check_ty(body), name, &*ty, &*val, &*body),
            _ => Err(format!("Unhandled type {:?}", expr))
        }
    }

    pub fn check_tm(&mut self, expr: &Expr) -> Result<(Tm, Ty), String> {
        match expr {
            Expr::App(id, v) =>
                match (id.as_str(), &v[..]) {
                    ("refl", [a]) => self.refl(&*a),
                    ("true", []) => Ok(self.true_tm()),
                    ("false", []) => Ok(self.false_tm()),
                    (v, []) => self.access_var(v),
                    (s, v) => Err(format!("Unexpected {} with {} args", s, v.len()))
                },
            Expr::Let { name, ty, val, body } =>
                self.check_let(|s, body| s.check_tm(body), name, &*ty, &*val, &*body),
            Expr::Elim { val, into_ctx, into_ty, cases } =>
                self.check_elim(&*val, into_ctx, &*into_ty, cases),
        }
    }

    fn refl(&mut self, expr: &Expr) -> Result<(Tm, Ty), String> {
        let (tm, _) = self.check_tm(expr)?;
        let eq_ty = self.model.eq_ty(&tm, &tm);
        let refl_tm = self.model.refl(&tm);
        Ok((refl_tm, eq_ty))
    }

    fn true_tm(&mut self) -> (Tm, Ty) {
        let cur_ctx_syn = &self.ctxs.last().unwrap().syntax;
        let bool_ty = self.model.bool_ty(cur_ctx_syn);
        let tm = self.model.true_tm(cur_ctx_syn);
        (tm, bool_ty)
    }

    fn false_tm(&mut self) -> (Tm, Ty) {
        let cur_ctx_syn = &self.ctxs.last().unwrap().syntax;
        let bool_ty = self.model.bool_ty(cur_ctx_syn);
        let tm = self.model.false_tm(cur_ctx_syn);
        (tm, bool_ty)
    }

    // Given G |- a : A, construct the morphism <1(G), A, a> : G.A -> G
    // substituting the last A for a in any term in G.A.
    fn bar_tm(model: &mut TModel, ctx: &Ctx, ty: &Ty, tm: &Tm) -> Morph {
        let id = model.id_morph(ctx);
        model.extension(&id, ty, tm)
    }

    fn check_elim(
        &mut self,
        val: &Expr, into_ctx: &Vec<CtxExt>, into_ty: &Expr,
        cases: &Vec<ElimCase>) -> Result<(Tm, Ty), String>
    {
        let (val_tm, val_ty) = self.check_tm(val)?;
        let bool_ty = self.model.bool_ty(&self.ctxs.last().unwrap().syntax);

        let (elim_tm, elim_ty) =
            if self.model.ty_eq(&val_ty, &bool_ty) {
                self.elim_bool(into_ctx, into_ty, cases)?
            } else {
                return Err(format!("Cannot eliminate {:?} of type {:?}", val, val_ty))
            };
        
        // Substitute bar(val_tm) into elimination term and type, which live
        // live in an extended context.
        let cur_ctx_syn = &self.ctxs.last().unwrap().syntax;
        let bar = Self::bar_tm(&mut self.model, cur_ctx_syn, &val_ty, &val_tm);
        let tm = self.model.subst_tm(&bar, &elim_tm);
        let ty = self.model.subst_ty(&bar, &elim_ty);
        Ok((tm, ty))
    }

    fn elim_bool(
        &mut self,
        into_ctx: &Vec<CtxExt>, into_ty: &Expr,
        cases: &Vec<ElimCase>) -> Result<(Tm, Ty), String>
    {
        if into_ctx.len() != 1 || cases.len() != 2 ||
           cases[0].0.len() != 0 || cases[1].0.len() != 0
        {
            return Err("Invalid bool elimination".to_owned())
        }

        let bool_ty = self.model.bool_ty(&self.ctxs.last().unwrap().syntax);
        let into_ty = {
            let mut s = self.save_ctx();
            let ext_ty = s.extend(&into_ctx[0])?;
            if !s.model.ty_eq(&ext_ty, &bool_ty) {
                return Err("Invalid extension for into-type: expected bool".to_owned());
            }
            
            s.check_ty(into_ty)?
        };

        let cur_ctx_syn = &self.ctxs.last().unwrap().syntax;
        let true_tm = self.model.true_tm(cur_ctx_syn);
        let true_bar = Self::bar_tm(&mut self.model, cur_ctx_syn, &bool_ty, &true_tm);
        let expected_ty_true_case = Self::subst_ty(&mut self.model, &true_bar, &into_ty);

        let false_tm = self.model.false_tm(cur_ctx_syn);
        let false_bar = Self::bar_tm(&mut self.model, cur_ctx_syn, &bool_ty, &false_tm);
        let expected_ty_false_case = Self::subst_ty(&mut self.model, &false_bar, &into_ty);

        let true_case_tm = self.check_tm_ty(&cases[0].1, &expected_ty_true_case)?;
        let false_case_tm = self.check_tm_ty(&cases[1].1, &expected_ty_false_case)?;

        let cur_ctx_syn = &self.ctxs.last().unwrap().syntax;
        let tm = self.model.elim_bool(cur_ctx_syn, &into_ty, &true_case_tm, &false_case_tm);
        Ok((tm, into_ty))
    }

    fn check_tm_ty(&mut self, expr: &Expr, expected_ty: &Ty) -> Result<Tm, String> {
        let (tm, ty) = self.check_tm(expr)?;
        if self.model.ty_eq(&ty, expected_ty) {
            Ok(tm)
        } else {
            Err(format!("expected:\n{:#?}\ngot:\n{:#?}", expected_ty, ty))
        }
    }

    fn access_var(&mut self, name: &str) -> Result<(Tm, Ty), String> {
        let mut ctx_index = self.ctxs.len();
        for ctx in self.ctxs.iter().rev() {
            ctx_index -= 1;
            for (ref ctx_var_name, ref tm, ref ty) in ctx.defs.iter().rev() {
                if ctx_var_name != name {
                    continue
                }

                let mut tm = tm.clone();
                let mut ty = ty.clone();
                // Found term, inject it into current context.
                for ctx in &self.ctxs[ctx_index+1..] {
                    let weakening = match ctx.weakening {
                        Some(ref w) => w,
                        None => panic!("expected weakening to be available")
                    };
                    tm = Self::subst_tm(&mut self.model, &weakening, &tm);
                    ty = Self::subst_ty(&mut self.model, &weakening, &ty);
                }

                return Ok((tm, ty))
            }
        }

        Err(format!("unknown definition {}", name))
    }

    fn check_eq(&mut self, a: &Expr, b: &Expr) -> Result<Ty, String> {
        let (tma, tya) = self.check_tm(a)?;
        let tmb = self.check_tm_ty(b, &tya)?;
        Ok(self.model.eq_ty(&tma, &tmb))
    }

    fn subst_ty(model: &mut TModel, f: &Morph, ty: &Ty) -> Ty {
        Self::def_ty_rec(model, f, ty);
        model.subst_ty(f, ty)
    }

    fn subst_tm(model: &mut TModel, f: &Morph, tm: &Tm) -> Tm {
        Self::def_tm_rec(model, f, tm);
        model.subst_tm(f, tm)
    }

    fn def_morph_rec(model: &mut TModel, g: &Morph, f: &Morph) {
        match f {
            Morph::Composition(ref f, ref e) => {
                // g . (f . e)
                let comp = model.compose(g, &*f);
                Self::def_morph_rec(model, &comp, e);
            },
            //Morph::Extension(ref f, ref s, ref tm) {
            //    // g . <f, s, tm>
            //    let _comp = self.model.compose(g, f);
            //    self.def_morph_rec(g, &*f);
            //    let _tm = self.model.subst_tm(g, s)
            //}
            _ => ()
        }
    }

    fn def_ty_rec(model: &mut TModel, g: &Morph, ty: &Ty) {
        match ty {
            Ty::Subst(ref f, ref s) => {
                // g (f s) = (g . f) s
                let gf = model.compose(g, &*f);
                Self::def_morph_rec(model, g, &*f);
                model.subst_ty(&gf, &*s);
                Self::def_ty_rec(model, &gf, &*s);
            },
            Ty::Eq(ref a, ref b) => {
                let ga = model.subst_tm(g, &*a);
                Self::def_tm_rec(model, g, &*a);
                let gb = model.subst_tm(g, &*b);
                Self::def_tm_rec(model, g, &*b);

                model.eq_ty(&ga, &gb);
            },
            _ => ()
        }
    }

    fn def_tm_rec(model: &mut TModel, g: &Morph, tm: &Tm) {
        match tm {
            Tm::Subst(ref f, ref tm) => {
                // g (f tm) = (g . f) tm
                let gf = model.compose(g, &*f);
                Self::def_morph_rec(model, g, &*f);
                model.subst_tm(&gf, &*tm);
                Self::def_tm_rec(model, &gf, &*tm);
            },
            Tm::Refl(ref a) => {
                let ga = model.subst_tm(g, &*a);
                Self::def_tm_rec(model, g, &*a);
                model.refl(&ga);
            },
            _ => ()
        }
    }
}