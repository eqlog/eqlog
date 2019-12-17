using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using QT.Parse;
using Z3Expr = Microsoft.Z3.Expr;

namespace QT
{
    internal class TypeChecker : IDisposable
    {
        private readonly Context _ctx;
        private readonly Fixedpoint _fix;
        private readonly BitVecSort _tySort;
        private readonly BitVecSort _tmSort;
        private readonly FuncDecl _isTy;
        private readonly FuncDecl _isTm;
        private readonly FuncDecl _tyEq;
        private readonly FuncDecl _tmTy;
        private readonly FuncDecl _tmEq;

        public TypeChecker()
        {
            _ctx = new Context();
            _fix = _ctx.MkFixedpoint();
            _fix.Parameters =
                _ctx.MkParams()
                .Add("fp.engine", "datalog")
                .Add("datalog.generate_explanations", true);
            _tySort = _ctx.MkBitVecSort(3);
            _tmSort = _ctx.MkBitVecSort(32);
            _isTy = Relation("IsTy", _tySort);
            _isTm = Relation("IsTm", _tmSort);
            _tmTy = Relation("TmTy", _tmSort, _tySort);
            _tyEq = Relation("TyEq", _tySort, _tySort);
            _tmEq = Relation("TmEq", _tmSort, _tmSort);
            MakeEquivalence(_isTy, _tyEq);
            MakeEquivalence(_isTm, _tmEq);
            AddTmConv();

            _fix.AddFact(_isTy, 0);
            _fix.AddFact(_isTy, 1);
            _fix.AddFact(_isTy, 2);
            Console.WriteLine(_fix.Query(_isTy));
            Console.WriteLine(_fix.GetAnswer());
            Console.WriteLine(_fix.Query(_tyEq));
            Console.WriteLine(_fix.GetAnswer());
            _fix.AddFact(_tyEq, 0, 1);
            _fix.AddFact(_tyEq, 1, 2);
            Console.WriteLine(_fix.Query(_tyEq));
            Console.WriteLine(_fix.GetAnswer());
        }

        private FuncDecl Relation(string name, params Sort[] sorts)
        {
            FuncDecl decl = _ctx.MkFuncDecl(name, sorts, _ctx.BoolSort);
            _fix.RegisterRelation(decl);
            return decl;
        }

        private void MakeEquivalence(FuncDecl isSortRel, FuncDecl eqRel)
        {
            Debug.Assert(isSortRel.Domain.Length == 1 &&
                         isSortRel.Range == _ctx.BoolSort);
            Debug.Assert(eqRel.Domain.Length == 2 &&
                         eqRel.Domain.All(s => s == isSortRel.Domain[0]) &&
                         eqRel.Range == _ctx.BoolSort);
            Z3Expr a = _ctx.MkConst("a", eqRel.Domain[0]);
            Z3Expr b = _ctx.MkConst("b", eqRel.Domain[0]);
            Z3Expr c = _ctx.MkConst("c", eqRel.Domain[0]);
            string prefix = eqRel.Name.ToString();
            _fix.AddRule(
                    _ctx.MkForall(
                        new[]{a},
                        _ctx.MkImplies(
                            (BoolExpr)isSortRel.Apply(a),
                            (BoolExpr)eqRel.Apply(a, a))),
                    _ctx.MkSymbol($"{prefix}-Reflexive"));
            _fix.AddRule(
                    _ctx.MkForall(
                        new[]{a, b},
                        _ctx.MkImplies(
                            (BoolExpr)eqRel.Apply(a, b),
                            (BoolExpr)eqRel.Apply(b, a))),
                    _ctx.MkSymbol("{prefix}-Symmetric"));
            _fix.AddRule(
                    _ctx.MkForall(
                        new[]{a, b, c},
                        _ctx.MkImplies(
                            (BoolExpr)eqRel.Apply(a, b) &
                            (BoolExpr)eqRel.Apply(b, c),
                            (BoolExpr)eqRel.Apply(a, c))),
                    _ctx.MkSymbol("{prefix}-Transitive"));
        }

        private void AddTmConv()
        {
            Z3Expr tm = _ctx.MkConst("M", _tmSort);
            Z3Expr s = _ctx.MkConst("σ", _tySort);
            Z3Expr t = _ctx.MkConst("τ", _tySort);

            _fix.AddRule(
                    _ctx.MkForall(
                        new[]{tm, s, t},
                        _ctx.MkImplies(
                            (BoolExpr)_tmTy.Apply(tm, s) &
                            (BoolExpr)_tyEq.Apply(s, t),
                            (BoolExpr)_tmTy.Apply(tm, t))),
                    _ctx.MkSymbol("Tm-Conv"));
        }

        private uint _tyCounter;
        private uint FormId(uint tmTy, uint tmLeft, uint tmRight)
        {
            uint id = checked(++_tyCounter);
            _fix.AddFact(_isTy, id);

            // forall (O : Tm), TmTy O Id(M, N) => TmEq M N
            Z3Expr tm = _ctx.MkConst("M", _tmSort);
            _fix.AddRule(
                    _ctx.MkForall(
                        new[]{tm},
                        _ctx.MkImplies(
                            (BoolExpr)_tmTy.Apply(tm, _ctx.MkBV(id, _tySort.Size)),
                            (BoolExpr)_tmEq.Apply(
                                _ctx.MkBV(tmLeft, _tmSort.Size),
                                _ctx.MkBV(tmRight, _tmSort.Size)))),
                    _ctx.MkSymbol($"Id-{tmTy}-Reflection"));

            return id;
        }

        // Add a type to the model.
        private int Type(string name)
        {
            return 0;
        }

        private int Axiom(string type) => Axiom(AstParser.ParseExpr(type));

        // Add a term of the specified type to the model without any checks.
        private int Axiom(Expr type)
        {
            return 0;
        }

        private int TypeCheck(SyntaxNode node)
        {
            switch (node)
            {
                case Def def:
                    return 0;
            }

            return 0;
        }

        public bool Check(Def def, out string error)
        {
            error = "";
            return false;
        }

        public bool Check(Unit unit, out string error)
        {
            error = "";

            return false;
        }

        public void Dispose()
        {
            _ctx.Dispose();
        }
    }
}
