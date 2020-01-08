namespace QT
{
    internal interface IModel
    {
        bool CtxEq(Ctx l, Ctx r);
        bool MorphEq(CtxMorph l, CtxMorph r);
        bool TyEq(Ty l, Ty r);
        bool TmEq(Tm l, Tm r);

        EmptyCtx EmptyCtx();

        ComprehensionCtx Comprehension(Ctx baseCtx, Ty ty);
        ProjMorph ProjCtx(ComprehensionCtx ctx);
        ProjTm ProjTm(ComprehensionCtx ctx);

        IdMorph IdMorph(Ctx ctx);
        CompMorph Compose(CtxMorph g, CtxMorph f);
        ExtensionMorph Extension(CtxMorph morph, Tm tm, Ty compTy);

        SubstTy SubstType(Ty baseTy, CtxMorph morph);
        SubstTm SubstTerm(Tm baseTm, CtxMorph morph);

        IdTy Id(Tm left, Tm right);
        ReflTm Refl(Tm tm);

        BoolTy Bool(Ctx ctx);
        TrueTm True(Ctx ctx);
        FalseTm False(Ctx ctx);
        ElimBoolTm ElimBool(Ty intoTy, Tm trueCase, Tm falseCase);

        void Dump(string rels);
    }
}
