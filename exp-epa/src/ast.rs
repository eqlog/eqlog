#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Def {
    Dump {
        message: Option<String>,
    },
    Def {
        name: String,
        args: Vec<(String, Ty)>,
        ty: Ty,
        tm: Tm,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tm {
    Variable(String),
    Typed {
        tm: Box<Tm>,
        ty: Box<Ty>,
    },
    App {
        fun: String,
        args: Vec<Tm>,
    },
    Let {
        body: Vec<Def>,
        result: Box<Tm>,
    },
    UnitTm,
    ElimUnit {
        discriminee: Box<Tm>,
        var: String,
        into_ty: Box<Ty>,
        unit_case: Box<Tm>,
    },
    True,
    False,
    ElimBool {
        discriminee: Box<Tm>,
        var: String,
        into_ty: Box<Ty>,
        false_case: Box<Tm>,
        true_case: Box<Tm>,
    },
    Refl(Box<Tm>),
    Zero,
    Succ(Box<Tm>),
    ElimNat {
        discriminee: Box<Tm>,
        var: String,
        into_ty: Box<Ty>,
        zero_case: Box<Tm>,
        succ_case_nat_var: String,
        succ_case_prev_var: String,
        succ_case: Box<Tm>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    Unit,
    Bool,
    Eq(Box<Tm>, Box<Tm>),
    Nat,
}
