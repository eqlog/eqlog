using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Runtime.CompilerServices;

namespace QT
{
    internal abstract class CwfNode
    {
        public CwfNode(uint id)
            => Id = id;

        public uint Id { get; }

        public override string ToString()
            => $"#{Id:x8}";
    }

    internal abstract class Ctx : CwfNode
    {
        public Ctx(uint id) : base(id)
        { }
    }

    internal abstract class CtxMorph : CwfNode
    {
        public CtxMorph(uint id, Ctx domain, Ctx codomain) : base(id)
        {
            Domain = domain;
            Codomain = codomain;
        }

        public Ctx Domain { get; }
        public Ctx Codomain { get; }
    }

    internal abstract class Ty : CwfNode
    {
        public Ty(uint id, Ctx ctx) : base(id)
        {
            Ctx = ctx;
        }

        public Ctx Ctx { get; }
    }

    internal abstract class Tm : CwfNode
    {
        public Tm(uint id, Ty ty) : base(id)
            => Ty = ty;

        public Ty Ty { get; }
        public Ctx Ctx => Ty.Ctx;
    }

    internal class EmptyCtx : Ctx
    {
        public EmptyCtx(uint id) : base(id)
        { }

        public override string ToString()
            => $"T";
    }

    internal class ComprehensionCtx : Ctx
    {
        public ComprehensionCtx(uint id, Ctx baseCtx, Ty compTy) : base(id)
        {
            BaseCtx = baseCtx;
            CompTy = compTy;
        }

        public Ctx BaseCtx { get; }
        public Ty CompTy { get; }

        public override string ToString()
            => BaseCtx is EmptyCtx ? $"{CompTy}" : $"{BaseCtx}.{CompTy}";
    }

    internal class ProjMorph : CtxMorph
    {
        public ProjMorph(uint id, ComprehensionCtx ctx) : base(id, ctx, ctx.BaseCtx)
        {
        }

        public new ComprehensionCtx Domain => (ComprehensionCtx)base.Domain;

        public override string ToString()
            => $"p1({Domain})";
    }

    internal class ProjTm : Tm
    {
        public ProjTm(uint id, Ty ty) : base(id, ty)
        {
            Debug.Assert(ty.Ctx is ComprehensionCtx);
        }

        public new ComprehensionCtx Ctx => (ComprehensionCtx)base.Ctx;

        public override string ToString()
            => $"p2({Ctx})";
    }

    internal class IdMorph : CtxMorph
    {
        public IdMorph(uint id, Ctx ctx) : base(id, ctx, ctx)
        { }

        public override string ToString()
            => $"1({Domain})";
    }

    internal class CompMorph : CtxMorph
    {
        public CompMorph(uint id, CtxMorph g, CtxMorph f) : base(id, f.Domain, g.Codomain)
        {
            G = g;
            F = f;
        }

        public CtxMorph G { get; }
        public CtxMorph F { get; }

        public override string ToString()
            => $"{G} . {F}";
    }

    internal class ExtensionMorph : CtxMorph
    {
        public ExtensionMorph(uint id, CtxMorph morph, Tm tm, Ctx codomain) : base(id, morph.Domain, codomain)
        {
            Morph = morph;
            Tm = tm;
        }

        public CtxMorph Morph { get; }
        public Tm Tm { get; }

        public override string ToString()
            => $"<{Morph}, {Tm}>";
    }

    internal class SubstTy : Ty
    {
        public SubstTy(uint id, Ty baseTy, CtxMorph morph) : base(id, morph.Domain)
        {
            BaseTy = baseTy;
            Morph = morph;
        }

        public Ty BaseTy { get; }
        public CtxMorph Morph { get; }

        public override string ToString()
            => $"{BaseTy}{{{Morph}}}";
    }

    internal class SubstTm : Tm
    {
        public SubstTm(uint id, Tm baseTm, CtxMorph morph, Ty newTy) : base(id, newTy)
        {
            BaseTm = baseTm;
            Morph = morph;
        }

        public Tm BaseTm { get; }
        public CtxMorph Morph { get; }

        public override string ToString()
            => $"{BaseTm}{{{Morph}}}";
    }

    internal class IdTy : Ty
    {
        public IdTy(uint id, Tm left, Tm right) : base(id, left.Ctx)
        {
            Left = left;
            Right = right;
        }

        public Tm Left { get; }
        public Tm Right { get; }

        public override string ToString()
            => $"id({Left}, {Right})";
    }

    internal class ReflTm : Tm
    {
        public ReflTm(uint id, Tm eqTm, IdTy ty) : base(id, ty)
            => EqTm = eqTm;

        public Tm EqTm { get; }
        public new IdTy Ty => (IdTy)base.Ty;

        public override string ToString()
            => $"refl({EqTm})";
    }

    internal class BoolTy : Ty
    {
        public BoolTy(uint id, Ctx ctx) : base(id, ctx)
        { }

        public override string ToString()
            => $"bool";
    }

    internal class TrueTm : Tm
    {
        public TrueTm(uint id, BoolTy ty) : base(id, ty)
        {
        }

        public new BoolTy Ty => (BoolTy)base.Ty;

        public override string ToString()
            => $"true({Ctx})";
    }

    internal class FalseTm : Tm
    {
        public FalseTm(uint id, BoolTy ty) : base(id, ty)
        {
        }

        public new BoolTy Ty => (BoolTy)base.Ty;

        public override string ToString()
            => $"false({Ctx})";
    }

    internal class ElimBoolTm : Tm
    {
        public ElimBoolTm(uint id, Ty intoTy, Tm trueCase, Tm falseCase) : base(id, intoTy)
        {
            TrueCase = trueCase;
            FalseCase = falseCase;
        }

        public Tm TrueCase { get; }
        public Tm FalseCase { get; }

        public override string ToString()
            => $"elimb({TrueCase}, {FalseCase})";
    }
}
