pub type Id = String;
pub type DefId = Option<Id>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CtxExt(pub DefId, pub Expr);

pub type Unit = Vec<Def>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Def {
    pub name: DefId,
    pub ctx: Vec<CtxExt>,
    pub ret_ty: Expr,
    pub body: Expr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    App(Id, Vec<Expr>),
    Let { name: DefId,
          ty: Box<Expr>,
          val: Box<Expr>,
          body: Box<Expr> },
    Elim { val: Box<Expr>,
           into_ctx : Vec<CtxExt>,
           into_ty: Box<Expr>,
           cases: Vec<ElimCase> }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ElimCase(pub Vec<CtxExt>, pub Expr);