use eqlog::signature::*;
use eqlog::syntax::*;
use eqlog::closure::*;
use eqlog::model::*;
use eqlog::element::*;
use std::iter::once;

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

        ExtCtx: Ctx x Ty x Ctx,
        // (G, sigma) should be uniquely determined by G.sigma and ExtCtx(G, sigma, G.sigma)
        Wkn: Ctx -> Mor,
        // Wkn(D) should only be defined if D = G.sigma for (unique) G and sigma
        Var: Ctx -> Tm,
        // Var(D) should only be defined if D = G.sigma for (unique) G and sigma
        MorExt: Ctx x Mor x Tm -> Mor,
        // MorExt(D, f, s) should only be defined if D = Dom(f).sigma for some sigma

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

pub type Cwf = Model<CwfSignature>;

lazy_static! { static ref CWF_AXIOMS: Vec<CheckedSurjectionPresentation<CwfSignature>> =
    vec![
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
        // TODO: is the other direction needed?


        // context and type of substitutions
        sequent!(TyCtx(SubstTy(f, _)) ~> Cod(f)),
        sequent!(TmTy(SubstTm(f, s)) ~> SubstTy(f, TmTy(s))),

        // functoriality of substitution: identity
        sequent!(SubstTy(Id(TyCtx(sigma)), sigma) ~> sigma),
        sequent!(SubstTm(Id(TyCtx(TmTy(s))), s) ~> s),

        // functoriality of substitution: composition
        sequent!(SubstTy(g, SubstTy(f, sigma)) ~> SubstTy(Comp(g, f), sigma)),
        sequent!(SubstTm(g, SubstTm(f, s)) ~> SubstTm(Comp(g, f), s)),


        // domain and codomain of the weakening map
        sequent!(Cod(Wkn(Gsigma)) ~> Gsigma),
        sequent!(ExtCtx(G, _, Gsigma) => Dom(Wkn(Gsigma)) ~> G),

        // type of the variable
        sequent!(ExtCtx(_, sigma, Gsigma) => TmTy(Var(Gsigma)) ~> SubstTy(Wkn(Gsigma), sigma)),

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
            SubstTm(MorExt(Gbool, f, True(Cod(f))), BoolElim(sigma, true_case, _)) ~> true_case
        ),
        sequent!(
            TyCtx(sigma) = Gbool
            =>
            SubstTm(MorExt(Gbool, f, False(Cod(f))), BoolElim(sigma, _, false_case)) ~> false_case
        ),
        // Uniqueness of bool elimination
        sequent!(
            B = Bool(G) & ExtCtx(G, B, Gbool) & TyCtx(sigma) = Gbool & TmTy(s) = sigma &
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
    ].iter().
    map(|s| to_surjection_presentation(CwfSignature::new(), s).checked(CwfSignature::new())).
    chain(
        CwfSignature::new().relations().iter().
        filter(|r| r.kind() == RelationKind::Operation).
        map(|r| CheckedSurjectionPresentation::functionality(CwfSignature::new(), *r))
    ).
    collect();
}

#[test]
fn test_cwf_axioms() {
    let _ = *CWF_AXIOMS;
}

pub fn close_cwf(cwf: &mut Cwf) {
    close_model(CWF_AXIOMS.as_slice(), cwf);
}

pub fn eval_op(cwf: &Cwf, op: CwfRelation, args: &[Element]) -> Option<Element> {
    assert_eq!(op.kind(), RelationKind::Operation);

    let dom_len: usize = op.arity().len() - 1;
    let op_dom: &[CwfSort] = &op.arity()[.. dom_len];

    assert!(op_dom.iter().cloned().eq(args.iter().map(|arg| cwf.element_sort(*arg))));
    
    cwf.rows(op).filter(|row| &row[.. dom_len] == args).next().map(|row| *row.last().unwrap())
}

pub fn tm_ty(cwf: &Cwf, tm: Element) -> Option<Element> {
    eval_op(cwf, CwfRelation::TmTy, &[tm])
}

pub fn adjoin_op(cwf: &mut Cwf, op: CwfRelation, args: Vec<Element>) -> Element {
    assert_eq!(op.kind(), RelationKind::Operation);

    let dom_len: usize = op.arity().len() - 1;
    let op_dom: &[CwfSort] = &op.arity()[.. dom_len];
    let cod: CwfSort = *op.arity().last().unwrap();

    assert!(op_dom.iter().cloned().eq(args.iter().map(|arg| cwf.element_sort(*arg))));

    let result = cwf.adjoin_element(cod);
    let mut row = args;
    row.push(result);
    cwf.adjoin_rows(op, once(row));
    result
}

pub fn els_are_equal(cwf: &mut Cwf, lhs: Element, rhs: Element) -> bool {
    assert_eq!(cwf.element_sort(lhs), cwf.element_sort(rhs));
    cwf.representative(lhs) == cwf.representative(rhs)
}
