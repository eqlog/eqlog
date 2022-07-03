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
    UnitInd {
        name: String,
        var: String,
        into_ty: Ty,
        unit_case: Tm,
    },
    BoolInd {
        name: String,
        var: String,
        into_ty: Ty,
        false_case: Tm,
        true_case: Tm,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tm {
    Variable(String),
    Typed { tm: Box<Tm>, ty: Box<Ty> },
    App { fun: String, args: Vec<Tm> },
    Let { body: Vec<Def>, result: Box<Tm> },
    UnitTm,
    True,
    False,
    Refl(Box<Tm>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    Unit,
    Bool,
    Eq(Box<Tm>, Box<Tm>),
}
