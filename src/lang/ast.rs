#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Def {
    pub name: String,
    pub args: Vec<(String, Ty)>,
    pub ty: Ty,
    pub tm: Tm,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tm {
    Typed { tm: Box<Tm>, ty: Box<Ty> },
    App { fun: String, args: Vec<Tm> },
    Let { body: Vec<Def>, result: Box<Tm> },
    UnitTm,
    True,
    False,
    Neg(Box<Tm>),
    BoolElim {
        discriminee: Box<Tm>,
        into_var: String,
        into_ty: Box<Ty>,
        true_case: Box<Tm>,
        false_case: Box<Tm>,
    },
    Refl(Box<Tm>),
    Z,
    S(Box<Tm>),
    Ind {
        discriminee: Box<Tm>,
        into_var: String,
        into_ty: Box<Ty>,
        zero_case: Box<Tm>,
        succ_nat_var: String,
        succ_hyp_var: String,
        succ_hyp_ty: Box<Ty>,
        succ_tm: Box<Tm>,
    },
}


#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    Unit,
    Bool,
    Nat,
    Eq(Box<Tm>, Box<Tm>),
}
