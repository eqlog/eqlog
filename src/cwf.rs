use crate::eqlog::relational_structure::*;
use crate::eqlog::theory::*;

arities!{
    pub enum CwfSort {Ctx, Mor, Ty, Tm},
    pub enum CwfRelation {
        Dom: Mor -> Ctx,
        Cod: Mor -> Ctx,
        Comp: Mor x Mor -> Mor,
        Id: Ctx -> Mor,

        TyCtx: Ty -> Ctx,
        TmTy: Tm -> Ty,
        SubstTy: Mor x Ty-> Ty,
        SubstTm: Mor x Tm-> Tm,

        ExtCtx: Ctx x Ctx,
        // ExtCtx(G, D) should hold if a D is a (single step) extension of G
        // The variable, its type and weaking can be retrieved with the following:
        ExtTy: Ctx -> Ty,
        // ExtTy(D) must be defined if and only if Ext(G, D)
        Wkn: Ctx -> Mor,
        // Wkn(D) should only be defined if D = G.sigma for (unique) G and sigma
        Var: Ctx -> Tm,
        // Var(D) should only be defined if D = G.sigma for (unique) G and sigma
        MorExt: Ctx x Mor x Tm -> Mor,
        // MorExt(D, f, s) should only be defined if D = Dom(f).sigma for some sigma
        
        IterExtCtx: Ctx x Ctx, // the transitive closure of ExtCtx
        
        Unit: Ctx -> Ty,
        UnitTm: Ctx -> Tm,

        Bool: Ctx -> Ty,
        True: Ctx -> Tm,
        False: Ctx -> Tm,
        Neg: Tm -> Tm,
        BoolElim: Ty x Tm x Tm -> Tm, // BoolElim(sigma, true_case, false_case)
        // If BoolElim(sigma, true_case, false_case), then we should have TmTy(sigma) = G.Bool(G)
        // for some G and true_case: <id, true>(sigma), false_case: <id, false>(sigma)

        Eq: Tm x Tm -> Ty,
        Refl: Tm -> Tm,
    },
}

pub type CwfSignature = StaticSignature<CwfSort, CwfRelation>;

pub type Cwf = RelationalStructure<CwfSignature>;

lazy_static! { pub static ref CWF_AXIOMS: Vec<Sequent> = vec![
    // domain and codomain of identities
    sequent!(Dom(Id(x)) ~> x),
    sequent!(Cod(Id(x)) ~> x),

    // domain and codomain of composition
    sequent!(Dom(Comp(_, f)) ~> Dom(f)),
    sequent!(Cod(Comp(g, _)) ~> Cod(g)),

    // identity is a left and right identity
    sequent!(Comp(f, Id(Dom(f))) ~> f),
    sequent!(Comp(Id(Cod(f)), f) ~> f),
    //sequent!(i = Id(x) & Dom(f) = x => Comp(f, i) = f),
    //sequent!(i = Id(y) & Cod(f) = y => Comp(i, f) = f),
    // one direction is probably not needed

    // composition is associative
    sequent!(Comp(h, Comp(g, f)) ~> Comp(Comp(h, g), f)),
    sequent!(Comp(Comp(h, g), f) ~> Comp(h, Comp(g, f))),
    // TODO: is the other direction needed?


    // context and type of substitutions
    sequent!(TyCtx(SubstTy(f, _)) ~> Cod(f)),
    sequent!(TmTy(SubstTm(f, s)) ~> SubstTy(f, TmTy(s))),

    // functoriality of substitution: identity
    sequent!(SubstTy(Id(TyCtx(sigma)), sigma) ~> sigma),
    sequent!(SubstTm(Id(TyCtx(TmTy(s))), s) ~> s),

    // functoriality of substitution: composition
    sequent!(SubstTy(g, SubstTy(f, sigma)) ~> SubstTy(Comp(g, f), sigma)),
    sequent!(SubstTy(Comp(g, f), sigma) ~> SubstTy(g, SubstTy(f, sigma))),
    sequent!(SubstTm(g, SubstTm(f, s)) ~> SubstTm(Comp(g, f), s)),
    sequent!(SubstTm(Comp(g, f), s) ~> SubstTm(g, SubstTm(f, s))),


    // domain and codomain of the weakening map
    sequent!(Cod(Wkn(Gsigma)) ~> Gsigma),
    sequent!(ExtCtx(G, Gsigma) => Dom(Wkn(Gsigma)) ~> G),

    // type of the variable
    sequent!(TmTy(Var(Gsigma)) ~> SubstTy(Wkn(Gsigma), ExtTy(Gsigma))),

    // domain and codomain of extended morphisms
    sequent!(Cod(MorExt(_, f, _)) ~> Cod(f)),
    sequent!(Dom(MorExt(Gsigma, _, _)) ~> Gsigma),
    
    // base & variable compatibility of extended morphisms
    sequent!(Comp(MorExt(Gsigma, f, _), Wkn(Gsigma)) ~> f),
    sequent!(SubstTm(MorExt(Gsigma, _, s), Var(Gsigma)) ~> s),

    // uniqueness of extended morphisms
    sequent!(
        Comp(g, Wkn(Gsigma)) = f & SubstTm(g, Var(Gsigma)) = s
        =>
        g = MorExt(Gsigma, f, s)
    ),

    sequent!(ExtCtx(G, Gsigma) => IterExtCtx(G, Gsigma)),
    sequent!(IterExtCtx(G, D) & IterExtCtx(D, E) => IterExtCtx(G, E)),

    // context and types of unit constants
    sequent!(TyCtx(Unit(G)) ~> G),
    sequent!(TmTy(UnitTm(G)) ~> Unit(G)),

    // substitution stability of unit constants
    sequent!(SubstTy(f, Unit(Dom(f))) ~> Unit(Cod(f))),
    sequent!(SubstTm(f, UnitTm(Dom(f))) ~> UnitTm(Cod(f))),

    // uniquness of UniqueEl
    sequent!(TmTy(t) = Unit(G) => t = UnitTm(G)),

    // context and types of bool constants
    sequent!(TyCtx(Bool(G)) ~> G),
    sequent!(TmTy(True(G)) ~> Bool(G)),
    sequent!(TmTy(False(G)) ~> Bool(G)),
    sequent!(TmTy(Neg(b)) ~> TmTy(b)),

    // substitution stability of bool constants
    sequent!(SubstTy(f, Bool(Dom(f))) ~> Bool(Cod(f))),
    sequent!(SubstTm(f, True(Dom(f))) ~> True(Cod(f))),
    sequent!(SubstTm(f, False(Dom(f))) ~> False(Cod(f))),
    sequent!(SubstTm(f, Neg(b)) ~> Neg(SubstTm(f, b))),

    // computation rules for negation
    sequent!(Neg(True(G)) ~> False(G)),
    sequent!(Neg(False(G)) ~> True(G)),

    // type of bool elimination
    sequent!(TmTy(BoolElim(sigma, _, _)) ~> sigma),
    // substituting true and false into bool elimination
    sequent!(
        TyCtx(sigma) = Gbool
        =>
        SubstTm(MorExt(Gbool, f, True(Cod(f))), BoolElim(sigma, true_case, _))
        ~> SubstTm(f, true_case)
    ),
    sequent!(
        TyCtx(sigma) = Gbool
        =>
        SubstTm(MorExt(Gbool, f, False(Cod(f))), BoolElim(sigma, _, false_case))
        ~> SubstTm(f, false_case)
    ),
    // Uniqueness of bool elimination
    sequent!(
        ExtCtx(G, Gbool) & ExtTy(Gbool) = Bool(G) & TyCtx(sigma) = Gbool & TmTy(s) = sigma &
        SubstTm(MorExt(Gbool, id, True(G)), s) = s_true &
        SubstTm(MorExt(Gbool, id, False(G)), s) = s_false
        =>
        s = BoolElim(sigma, s_true, s_false)
    ),
    // TODO: is substitution stability of bool elimination necessary or will this follow from
    // uniqueness?

    // context of equality types
    sequent!(TyCtx(Eq(s, _)) ~> TyCtx(TmTy(s))),
    // substitution stability of equality types
    sequent!(SubstTy(f, Eq(s, t)) ~> Eq(SubstTm(f, s), SubstTm(f, t))),

    // type of refl
    sequent!(TmTy(Refl(s)) ~> Eq(s, s)),
    // substitution stability of refl (the equality follows from equality reflection)
    sequent!(SubstTm(f, Refl(s)) ~> Refl(SubstTm(f, s))),
    // equality reflection
    sequent!(eq_ty = Eq(s, t) & TmTy(e0) = eq_ty & TmTy(e1) = eq_ty => s = t & e0 = e1),
]; }

lazy_static!{
    pub static ref CWF_SIGNATURE: CwfSignature = CwfSignature::new();
    pub static ref CWF_THEORY: Theory<CwfSignature> = Theory::new(
        *CWF_SIGNATURE,
        CWF_AXIOMS.iter().cloned()
    );
}

#[test]
fn test_cwf_theory() {
    let _ = *CWF_THEORY;
}
