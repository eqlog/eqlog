use std::rc::Rc;

pub trait Sort {
    fn get_name(&self) -> &str;
}

pub struct SortVar<T: Sort> {
    name: String,
    sort: T
}

pub fn create_sort_var<T: Sort + Default>(name: &str) -> SortVar<T> {
    SortVar {
        name: name.to_string(),
        sort: Default::default()
    }
}

pub trait Relation {
    fn get_name(&self) -> &str;
    fn dom_sorts(&self) -> &[Box<dyn Sort>];
}

pub struct AppliedRelation {
    relation: Box<dyn Relation>,
    vars: Vec<String>
}

pub struct Clause {
    head: AppliedRelation,
    body: Vec<AppliedRelation>
}

pub struct PhlTheory {
    sorts: Vec<Box<dyn Sort>>,
    relations: Vec<Rc<dyn Relation>>,
    clauses: Vec<Clause>,
}

macro_rules! Sort {
    ($name:ident) => {
        #[derive(Default)]
        struct $name { }

        impl Sort for $name {
            fn get_name(&self) -> &str {
                stringify!($name)
            }
        }
    }
}

macro_rules! Rel {
    ($name:ident, $($id:ident, $ty:ident),+) => {
        struct $name {
            sorts: Vec<Box<dyn Sort>>
        }

        impl Relation for $name {
            fn get_name(&self) -> &str {
                stringify!($name)
            }

            fn dom_sorts(&self) -> &[Box<dyn Sort>] {
                &self.sorts
            }
        }

        impl Default for $name {
            fn default() -> Self {
                Self {
                    sorts: vec![$(Box::from($ty::default())),+]
                }
            }
        }

        impl $name {
            fn apply(&self, $($id: &SortVar<$ty>),+) -> AppliedRelation {
                AppliedRelation {
                    relation: Box::from($name::default()),
                    vars: vec![$($id.name.clone()),+]
                }
            }
        }

        let $name = Rc::new($name::default());
    };

    ($name:ident : $s1:ident) => { Rel!($name, a, $s1) };
    ($name:ident : $s1:ident * $s2:ident) => { Rel!($name, a, $s1, b, $s2) };
    ($name:ident : $s1:ident * $s2:ident * $s3:ident) => { Rel!($name, a, $s1, b, $s2, c, $s3) };
    ($name:ident : $s1:ident * $s2:ident * $s3:ident * $s4:ident) => { Rel!($name, a, $s1, b, $s2, c, $s3, d, $s4) };
    ($name:ident : $s1:ident * $s2:ident * $s3:ident * $s4:ident * $s5:ident) => { Rel!($name, a, $s1, b, $s2, c, $s3, d, $s4, e, $s5) };
}

macro_rules! Rule {
    ($($rel:ident($($var:ident),+))&+ -> $hrel:ident($($hvar:ident),+) with $($v:ident) +) => {{
        $(let $v = create_sort_var(stringify!($v));)+
        let head = $hrel.apply($(&$hvar),+);
        let body = vec![$($rel.apply($(&$var),+)),+];
        Clause { head, body }
    }}
}

#[allow(non_snake_case)]
pub fn get_dptt() -> PhlTheory {
    Sort!(Ctx);
    Sort!(CtxMorph);
    Sort!(Ty);
    Sort!(Tm);
    Rel!(TyCtx : Ty * Ctx);
    Rel!(CtxEq : Ctx * Ctx);
    let ty_ctx_functional = Rule!(TyCtx(s, G) & TyCtx(s, D) -> CtxEq(G, D) with s G D);
    let ctx_eq_sym = Rule!(CtxEq(G, D) -> CtxEq(D, G) with G D);
    let ctx_eq_trans = Rule!(CtxEq(G, D) & CtxEq(D, E) -> CtxEq(G, E) with G D E);
    PhlTheory {
        sorts: vec![Box::new(Ctx {}), Box::new(CtxMorph {}), Box::new(Ty {}), Box::new(Tm {})],
        relations: vec![CtxEq],
        clauses: vec![ty_ctx_functional, ctx_eq_sym, ctx_eq_trans]
    }
}