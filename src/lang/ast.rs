#![allow(dead_code)]

pub struct Unit {
    pub defs: Vec<Def>
}

pub struct Def {
    pub name: Box<DefId>,
    pub params: Vec<CtxExt>,
    pub ret_ty: Box<Expr>,
    pub body: Box<Expr>,
}

pub struct DefId(pub Option<String>);

pub struct CtxExt {
    pub name: Box<DefId>,
    pub ty: Box<Expr>,
}

pub enum Expr {
    Id(String),
    App {fun: String, args: Vec<Expr>},
    Let {name: DefId, ty: Box<Expr>, val: Box<Expr>, body: Box<Expr>},
    Elim {expr: Box<Expr>, into_ext: Box<CtxExt>, cases: Vec<ElimCase>},
}

pub struct ElimCase {
    pub case_exts: Vec<CtxExt>,
    pub body: Box<Expr>,
}