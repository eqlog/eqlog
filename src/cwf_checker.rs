use crate::ast;
use crate::cwf::*;
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Checking {
    Yes,
    No,
}

#[derive(Clone, Debug)]
struct Definition {
    ambient_ctx: Ctx,
    extensions: Vec<ExtCtx>,
    tm: Tm,
}

#[derive(Clone, Debug)]
pub struct Scope {
    definitions: HashMap<String, Definition>,
    extensions: Vec<Ctx>,
    cwf: Cwf,
}

impl Scope {
    fn new() -> Self {
        let mut cwf = Cwf::new();
        let empty_ctx = cwf.new_ctx();
        Scope {
            definitions: HashMap::new(),
            extensions: vec![empty_ctx],
            cwf,
        }
    }
}

impl Scope {
    fn add_type(&mut self, checking: Checking, ty: &ast::Ty) -> Ty {
        match ty {
            ast::Ty::Unit => self.cwf.define_unit(*self.extensions.last().unwrap()),
            ast::Ty::Eq(lhs, rhs) => {
                let lhs = self.add_term(checking, lhs);
                let rhs = self.add_term(checking, rhs);

                if checking == Checking::Yes {
                    let lhs_ty = self.cwf.define_tm_ty(lhs);
                    let rhs_ty = self.cwf.define_tm_ty(lhs);
                    self.cwf.close();
                    assert_eq!(self.cwf.ty_root(lhs_ty), self.cwf.ty_root(rhs_ty));
                }
                self.cwf.define_eq(lhs, rhs)
            }
        }
    }
    fn add_term(&mut self, checking: Checking, tm: &ast::Tm) -> Tm {
        match tm {
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
            ast::Tm::App { .. } => panic!(),
            ast::Tm::Let { .. } => panic!(),
            ast::Tm::UnitTm => self.cwf.define_unit_tm(*self.extensions.last().unwrap()),
            ast::Tm::Refl(s) => {
                let s = self.add_term(checking, s);
                self.cwf.define_refl(s)
            }
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
                ambient_ctx: *self.extensions.last().unwrap(),
                extensions: Vec::new(),
                tm: var,
            },
        );
    }
    // Extend context by a variable.
    fn extend_context(&mut self, checking: Checking, name: &str, ty: &ast::Ty) {
        let ty = self.add_type(checking, ty);
        let base_ctx = *self.extensions.last().unwrap();
        let ext_ctx = self.cwf.define_ext_ctx(base_ctx, ty);
        let var = self.cwf.define_var(base_ctx, ty);
        self.extensions.push(ext_ctx);
        self.definitions.insert(
            name.to_string(),
            Definition {
                ambient_ctx: ext_ctx,
                extensions: Vec::new(),
                tm: var,
            },
        );
    }

    //pub fn add_definition(&mut self, checking: Checking, def: &ast::Def) {
    //    panic!();
    //    use ast::Def::*;
    //    match def {
    //        Dump => {
    //            println!("{:?}", self.cwf);
    //        }
    //        Def { name, args, ty, tm } => {
    //            if checking == Checking::Yes {
    //                let mut copy = self.clone();
    //                for (arg_var, arg_ty) in args.iter() {
    //                    copy.adjoin_variable(Checking::Yes, arg_var, arg_ty);
    //                }
    //                copy.add_term(Checking::Yes, tm);
    //            }
    //        }
    //        UnitInd { name, var, into_ty, unit_case } => {
    //        }
    //    }
    //}
}
