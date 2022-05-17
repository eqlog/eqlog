#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Def {
    Dump,
    Def { name: String, args: Vec<(String, Ty)>, ty: Ty, tm: Tm },
    UnitInd {
        name: String,
        var: String,
        into_ty: Ty,
        unit_case: Tm,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tm {
    Typed { tm: Box<Tm>, ty: Box<Ty> },
    App { fun: String, args: Vec<Tm> },
    Let { body: Vec<Def>, result: Box<Tm> },
    UnitTm,
    Refl(Box<Tm>),
}


#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    Unit,
    Eq(Box<Tm>, Box<Tm>),
}
