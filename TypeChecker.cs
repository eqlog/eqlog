using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using QT.Parse;
using Z3Expr = Microsoft.Z3.Expr;
using System.Collections.Immutable;

namespace QT
{
    internal class TypeChecker : IDisposable
    {
        private readonly Context _ctx;
        private readonly Fixedpoint _fix;
        private readonly BitVecSort _tmSort;
        private readonly FuncDecl _isTy;
        private readonly FuncDecl _isId;
        private readonly FuncDecl _tmTy;
        private readonly FuncDecl _tmEq;
        private uint _tmCounter;
        private ImmutableDictionary<string, uint> _context = ImmutableDictionary.Create<string, uint>();

        public TypeChecker()
        {
            _ctx = new Context();
            _fix = _ctx.MkFixedpoint();
            _fix.Parameters =
                _ctx.MkParams()
                .Add("fp.engine", "datalog")
                .Add("datalog.generate_explanations", true);
            _tmSort = _ctx.MkBitVecSort(32);
            _isTy = Relation("IsTy", _tmSort);
            _isId = Relation("IsId", _tmSort, _tmSort, _tmSort);
            _tmTy = Relation("TmTy", _tmSort, _tmSort);
            _tmEq = Relation("TmEq", _tmSort, _tmSort);
            MakeEquivalence(_isTy, _tmEq);
            AddTmConv();

            _fix.AddFact(_isTy, _tmCounter);
            _context = _context.Add("nat", _tmCounter++);

            _fix.AddFact(_tmTy, _tmCounter, _context["nat"]);
            _context = _context.Add("O", _tmCounter++);
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
            Z3Expr s = _ctx.MkConst("σ", _tmSort);
            Z3Expr t = _ctx.MkConst("τ", _tmSort);

            _fix.AddRule(
                    _ctx.MkForall(
                        new[]{tm, s, t},
                        _ctx.MkImplies(
                            (BoolExpr)_tmTy.Apply(tm, s) &
                            (BoolExpr)_tmEq.Apply(s, t),
                            (BoolExpr)_tmTy.Apply(tm, t))),
                    _ctx.MkSymbol("Tm-Conv"));
        }

        private uint FormId(uint tmLeft, uint tmRight)
        {
            Z3Expr s = _ctx.MkConst("σ", _tmSort);
            Status status =
                _fix.Query(
                    _ctx.MkExists(
                        new[] { s },
                        (BoolExpr)_tmTy.Apply(TmBV(tmLeft), s) &
                        (BoolExpr)_tmTy.Apply(TmBV(tmRight), s)));

            if (status != Status.SATISFIABLE)
            {
                throw new Exception("Cannot form id type");
            }

            uint id = checked(_tmCounter++);
            _fix.AddFact(_isTy, id);

            Z3Expr m = _ctx.MkConst("M", _tmSort);
            Z3Expr n = _ctx.MkConst("N", _tmSort);
            // Equality reflection
            _fix.AddRule(
                _ctx.MkForall(
                    new[]{m},
                    _ctx.MkImplies(
                        (BoolExpr)_tmTy.Apply(m, TmBV(id)),
                        (BoolExpr)_tmEq.Apply(TmBV(tmLeft), TmBV(tmRight)))),
                _ctx.MkSymbol($"Id-{id}-Reflection"));

            return id;
        }

        private uint IntroduceId(uint tm)
        {
            uint id = FormId(tm, tm);
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

        public uint TypeCheck(Def def)
        {
            ImmutableDictionary<string, uint> old = _context;
            foreach (CtxExt ctxExt in def.CtxExts)
            {
                uint typeId = TypeCheckType(ctxExt.Type);
                uint varId = _tmCounter++;
                _fix.AddFact(_tmTy, varId, typeId);
                _context = _context.SetItem(ctxExt.Name, varId);
            }

            uint resultTypeId = TypeCheckType(def.RetTy);
            uint bodyId = TypeCheck(def.Body);
            if (_fix.Query((BoolExpr)_tmTy.Apply(TmBV(bodyId), TmBV(resultTypeId))) == Status.SATISFIABLE)
            {
                _context = old.SetItem(def.Name, bodyId);
                return bodyId;
            }

            throw new Exception($"{def.Name}: Body does not type check to {def.RetTy}");
        }

        private uint TypeCheckType(Expr expr)
        {
            uint id = TypeCheck(expr);
            if (_fix.Query((BoolExpr)_isTy.Apply(TmBV(id))) == Status.SATISFIABLE)
                return id;

            throw new Exception($"Expected type, got {expr}");
        }

        private uint TypeCheck(Expr expr)
        {
            switch (expr)
            {
                case LetExpr let:
                    ImmutableDictionary<string, uint> old = _context;
                    uint resultTypeId = TypeCheckType(let.Type);
                    _context = _context.SetItem(let.Name, TypeCheck(let.Val));
                    uint bodyId = TypeCheck(let.Body);
                    if (_fix.Query((BoolExpr)_tmTy.Apply(TmBV(bodyId), TmBV(resultTypeId))) == Status.SATISFIABLE)
                    {
                        _context = old;
                        return bodyId;
                    }

                    throw new Exception($"let {let.Name}: Body does not type check to {let.Type}");
                case IdExpr id:
                    return _context[id.Id];
                case AppExpr app:
                    if (app.Fun == "id")
                        return FormId(TypeCheck(app.Args[0]), TypeCheck(app.Args[1]));
                    if (app.Fun == "refl")
                        return IntroduceId(TypeCheck(app.Args.Single()));
                    throw new Exception("Invalid function to apply " + app.Fun);
                default:
                    throw new Exception("Cannot handle yet");
            }
        }

        private BitVecNum TmBV(uint id)
            => _ctx.MkBV(id, _tmSort.Size);

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
