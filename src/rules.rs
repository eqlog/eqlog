use std::rc::Rc;

pub trait Sort {
    fn get_name(&self) -> &str;
}

pub trait Relation {
    fn get_name(&self) -> &str;
    fn dom_sorts(&self) -> &[Rc<dyn Sort>];
}

pub struct Clause {
}

pub struct PhlTheory {
    sorts: Vec<Rc<dyn Sort>>,
    relations: Vec<Rc<dyn Relation>>,
    clauses: Vec<Clause>,
}

macro_rules! Sort {
    ($name:ident) => {
        struct $name { }

        impl Sort for $name {
            fn get_name(&self) -> &str {
                stringify!($name)
            }
        }

        let $name = Rc::new($name { });
    }
}

macro_rules! Rel {
    ($name:ident, $($s:ident),+) => {
        struct $name {
            sorts: Vec<Rc<dyn Sort>>
        }

        impl Relation for $name {
            fn get_name(&self) -> &str {
                stringify!($name)
            }

            fn dom_sorts(&self) -> &[Rc<dyn Sort>] {
                &self.sorts
            }
        }

        let $name = Rc::new($name { sorts: vec![$($s.clone()),+] });
    };

    ($name:ident : $s1:ident) => { Rel!($name, $s1) };
    ($name:ident : $s1:ident * $s2:ident) => { Rel!($name, $s1, $s2) };
    ($name:ident : $s1:ident * $s2:ident * $s3:ident) => { Rel!($name, $s1, $s2, $s3) };
    ($name:ident : $s1:ident * $s2:ident * $s3:ident * $s4:ident) => { Rel!($name, $s1, $s2, $s3, s4) };
    ($name:ident : $s1:ident * $s2:ident * $s3:ident * $s4:ident * $s5:ident) => { Rel!($name, $s1, $s2, $s3, $s4, $s5) };
}

macro_rules! Rule {
    ($hrel:ident($($hvars:ident),+) :- $($rel:ident($($var:ident),+)),+) => {
        println!("Matched {}", stringify!($($rel),+))
    }
}

#[allow(non_snake_case)]
pub fn get_dptt() -> PhlTheory {
    Sort!(CtxS);
    Sort!(CtxMorphS);
    Sort!(TyS);
    Sort!(TmS);
    Rel!(CtxEq : CtxS * CtxS);
    Rule!(CtxEq(G, D) :- CtxEq(G, D), CtxEq(D, G));
    Rule!(CtxEq(G, E) :- CtxEq(G, D), CtxEq(D, E));
    PhlTheory {
        sorts: vec![CtxS, CtxMorphS, TyS, TmS],
        relations: vec![CtxEq],
        clauses: vec![]
    }
}