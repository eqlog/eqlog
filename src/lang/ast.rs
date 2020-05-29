use crate::eqlog::element::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Def {
    Def { name: String, args: Vec<(String, Ty)>, ty: Ty, tm: Tm },
    BoolInd {
        name: String,
        into_var: String,
        into_ty: Ty,
        true_case: Tm,
        false_case: Tm,
    },
    NatInd {
        name: String,
        into_var: String,
        into_ty: Ty,
        zero_case: Tm,
        succ_nat_var: String,
        succ_hyp_var: String,
        succ_hyp_ty: Ty,
        succ_tm: Tm,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tm {
    AlreadyAdded(Element),
    Typed { tm: Box<Tm>, ty: Box<Ty> },
    App { fun: String, args: Vec<Tm> },
    Let { body: Vec<Def>, result: Box<Tm> },
    UnitTm,
    True,
    False,
    Neg(Box<Tm>),
    Refl(Box<Tm>),
    Z,
    S(Box<Tm>),
}


#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    AlreadyAdded(Element),
    Unit,
    Bool,
    Nat,
    Eq(Box<Tm>, Box<Tm>),
}
