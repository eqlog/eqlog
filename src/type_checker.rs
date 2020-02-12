use scopeguard::{guard, ScopeGuard};
use super::model::Model;
use super::cwf::*;
use super::lang::ast::*;

pub struct TypeChecker<T: Model> {
    model: T,
    ctx : CtxInfo,
}

struct CtxExtension {
    prev_ctx: Ctx,
    ty: Ty,
    defs: Vec<Tm>
}

struct CtxInfo {
    extensions: Vec<CtxExtension>,
    ctx: Ctx
}

impl<T: Model> TypeChecker<T> {
    pub fn new(mut model: T) -> TypeChecker<T> {
        let empty = model.empty_ctx();
        TypeChecker {
            model: model,
            ctx: CtxInfo {
                extensions: Vec::new(),
                ctx: empty
            }
        }
    }

    pub fn check_def(&mut self, def: &Def) -> Result<Tm, String> {
        let mut s = guard(self, |mut s| s.called_after());
        let test = s.model.empty_ctx();
        println!("this looks like the last line");
        Err(format!("{:?}", test).to_string())
    }

    pub fn called_after(&mut self) {
        println!("called_after")
    }
}