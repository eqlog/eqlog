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

impl<T: Model> TypeChecker<T> {
    pub fn new(mut model: T) -> TypeChecker<T> {
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
            ScopeGuard<&mut TypeChecker<T>, impl FnOnce(&'a mut TypeChecker<T>)>
    {
        let depth = self.ctxs.len();
        assert!(depth > 0); // always have empty context
        let num_defs = self.ctxs.last().unwrap().defs.len();
        guard(self, move |s| {
            s.ctxs.truncate(depth);
            s.ctxs.last_mut().unwrap().defs.truncate(num_defs);
        })
    }

    fn extend(&mut self, ext: &CtxExt) -> Result<(), String> {
        let ty = self.check_ty(&ext.1)?;
        let new_ctx = self.model.comprehension(&ty);
        let weakening = self.model.weakening(&ty);
        let mut defs = vec![];

        if let Some(ref name) = ext.0 {
            let var_ty = self.model.subst_ty(&weakening, &ty);
            defs.push(((*name).clone(), self.model.var(&ty), var_ty))
        }
        
        let new_ctx_info = CtxInfo {
            syntax: new_ctx,
            weakening: Some(weakening),
            defs: defs
        };

        self.ctxs.push(new_ctx_info);
        Ok(())
    }

    pub fn check_def(&mut self, def: &Def) -> Result<Tm, String> {
        let mut s = self.save_ctx();
        for ext in def.ctx.iter() {
            s.extend(ext)?
        }
        let ret_ty = s.check_ty(&def.ret_ty)?;
        s.check_tm_ty(&def.body, &ret_ty)
    }

    pub fn check_ty(&mut self, expr: &Expr) -> Result<Ty, String> {
        let ctx_syn = &self.ctxs.last().unwrap().syntax;
        match expr {
            Expr::App(id, v) =>
                match (id.as_str(), &v[..]) {
                    ("bool", &[]) => Ok(self.model.bool_ty(ctx_syn)),
                    (s, v) => Err(format!("Unexpected {} with {} args", s, v.len()))
                },
            _ => Err(format!("Expected type, got {:?}", expr))
        }
    }

    pub fn check_tm(&mut self, expr: &Expr) -> Result<(Tm, Ty), String> {
        match expr {
            Expr::App(id, v) =>
                match (id.as_str(), &v[..]) {
                    // Variable
                    (v, []) => self.access_var(v),
                    (s, v) => Err(format!("Unexpected {} with {} args", s, v.len()))
                },
            _ => Err(format!("Unhandled term {:?}", expr))
        }
    }

    fn check_tm_ty(&mut self, expr: &Expr, expected_ty: &Ty) -> Result<Tm, String> {
        let (tm, ty) = self.check_tm(expr)?;
        if self.model.ty_eq(&ty, expected_ty) {
            Ok(tm)
        } else {
            Err(format!("expected: {:?}\ngot: {:?}", expected_ty, ty))
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

                let mut tm = (*tm).clone();
                let mut ty = (*ty).clone();
                // Found term, inject it into current context.
                for ctx in &self.ctxs[ctx_index+1..] {
                    let weakening = match ctx.weakening {
                        Some(ref w) => w,
                        None => panic!("expected weakening to be available")
                    };
                    tm = self.model.subst_tm(&weakening, &tm);
                    ty = self.model.subst_ty(&weakening, &ty);
                }

                return Ok((tm, ty))
            }
        }

        Err(format!("unknown definition {}", name))
    }
}