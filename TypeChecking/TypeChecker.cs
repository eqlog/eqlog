using Microsoft.Z3;
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics;
using System.Linq;
using System.Text.RegularExpressions;
using QT.Parse;
using Z3Expr = Microsoft.Z3.Expr;

namespace QT
{
    internal class TypeChecker : IDisposable
    {
        private const int SortSize = 32;

        private readonly Context _z3Ctx;
        private readonly Fixedpoint _fix;

        private readonly BitVecSort _sort;

        private readonly FuncDecl _ctxEq;
        private readonly FuncDecl _ctxMorphEq;
        private readonly FuncDecl _tyEq;
        private readonly FuncDecl _tmEq;

        private readonly FuncDecl _ctx;
        private readonly FuncDecl _ctxMorph;
        private readonly FuncDecl _comp;
        private readonly FuncDecl _ty;
        private readonly FuncDecl _tmTy;
        private readonly FuncDecl _idMorph;
        private readonly FuncDecl _tySubst;
        private readonly FuncDecl _tmSubst;

        private readonly FuncDecl _ctxEmpty;
        private readonly FuncDecl _comprehension;
        private readonly FuncDecl _projCtx;
        private readonly FuncDecl _projTm;
        private readonly FuncDecl _extension;

        private readonly FuncDecl _id;
        private readonly FuncDecl _refl;

        private readonly FuncDecl _bool;
        private readonly FuncDecl _true;
        private readonly FuncDecl _false;
        private readonly FuncDecl _boolElim;

        private readonly FuncDecl _nat;
        private readonly FuncDecl _zero;
        private readonly FuncDecl _succ;
        private readonly FuncDecl _natElim;

        private readonly Z3Expr _A, _B, _C, _D, _E, _F, _G;
        private readonly Z3Expr _f, _g, _gf;
        private readonly Z3Expr _s, _t;
        private readonly Z3Expr _M, _N;

        private readonly Dictionary<string, FuncDecl> _rels;

        private uint _counter;
        private uint NextId() => checked(++_counter);

        private readonly Dictionary<uint, string> _debugInfo = new Dictionary<uint, string>();

        private readonly ContextInfo _ctxInfo;

        public TypeChecker()
        {
            _z3Ctx = new Context();
            _fix = _z3Ctx.MkFixedpoint();
            _fix.Parameters =
                _z3Ctx.MkParams()
                //.Add("engine", "spacer")
                //.Add("datalog.generate_explanations", true)
                //.Add("datalog.explanations_on_relation_level", true)
                //.Add("datalog.all_or_nothing_deltas", true)
                //.Add("datalog.unbound_compressor", false)
                ;
            _fix.ParseString(s_z3Setup);

            _sort = _z3Ctx.MkBitVecSort(SortSize);
            _A = _z3Ctx.MkConst("A", _sort);
            _B = _z3Ctx.MkConst("B", _sort);
            _C = _z3Ctx.MkConst("C", _sort);
            _D = _z3Ctx.MkConst("D", _sort);
            _E = _z3Ctx.MkConst("E", _sort);
            _F = _z3Ctx.MkConst("F", _sort);
            _G = _z3Ctx.MkConst("G", _sort);
            _f = _z3Ctx.MkConst("f", _sort);
            _g = _z3Ctx.MkConst("g", _sort);
            _gf = _z3Ctx.MkConst("gf", _sort);
            _s = _z3Ctx.MkConst("s", _sort);
            _t = _z3Ctx.MkConst("t", _sort);
            _M = _z3Ctx.MkConst("M", _sort);
            _N = _z3Ctx.MkConst("N", _sort);

            _rels = CollectRelations(_fix.Rules);
            _ctxEq = _rels["CtxEq"];
            _ctxMorphEq = _rels["CtxMorphEq"];
            _tyEq = _rels["TyEq"];
            _tmEq = _rels["TmEq"];
            _ctx = _rels["Ctx"];
            _ctxMorph = _rels["CtxMorph"];
            _comp = _rels["Comp"];
            _ty = _rels["Ty"];
            _tmTy = _rels["TmTy"];
            _idMorph = _rels["IdMorph"];
            _tySubst = _rels["TySubst"];
            _tmSubst = _rels["TmSubst"];
            _ctxEmpty = _rels["CtxEmpty"];
            _comprehension = _rels["Comprehension"];
            _projCtx = _rels["ProjCtx"];
            _projTm = _rels["ProjTm"];
            _extension = _rels["Extension"];
            _id = _rels["Id"];
            _refl = _rels["Refl"];
            _bool = _rels["Bool"];
            _true = _rels["True"];
            _false = _rels["False"];
            _boolElim = _rels["BoolElim"];
            _nat = _rels["Nat"];
            _zero = _rels["Zero"];
            _succ = _rels["Succ"];
            _natElim = _rels["NatElim"];

            ModelCtx emptyCtx = NewCtx("");
            AddFact(_ctxEmpty, emptyCtx.Id);
            _ctxInfo = new ContextInfo(this, emptyCtx);
        }

        private static Dictionary<string, FuncDecl> CollectRelations(IEnumerable<Z3Expr> exprs)
        {
            var decls = new Dictionary<string, FuncDecl>();
            var queue = new Queue<Z3Expr>(exprs);
            var seen = new HashSet<uint>();

            void Enqueue(Z3Expr expr)
            {
                if (seen.Add(expr.Id))
                    queue.Enqueue(expr);
            }

            foreach (Z3Expr expr in exprs)
                Enqueue(expr);

            while (queue.Count > 0)
            {
                Z3Expr expr = queue.Dequeue();
                if (expr.IsApp)
                {
                    if (!expr.IsAnd && !expr.IsImplies)
                        decls[expr.FuncDecl.Name.ToString()] = expr.FuncDecl;

                    foreach (Z3Expr arg in expr.Args)
                        Enqueue(arg);
                }
                else if (expr.IsQuantifier)
                {
                    Enqueue(((Quantifier)expr).Body);
                }
            }

            return decls;
        }

        private T WithDbg<T>(T obj) where T : ModelObject
        {
            if (_debugInfo.TryGetValue(obj.Id, out string? dbg))
                ModelObject.DbgInfo.Add(obj, dbg);

            return obj;
        }

        private string ShortestDbgString(ModelCtx ctx) => ShortestDbgString(ctx, _ctxEq);
        private string ShortestDbgString(CtxMorphism morph) => ShortestDbgString(morph, _ctxMorphEq);
        private string ShortestDbgString(Ty ty) => ShortestDbgString(ty, _tyEq);
        private string ShortestDbgString(Tm tm) => ShortestDbgString(tm, _tmEq);

        private string ShortestDbgString(ModelObject obj, FuncDecl eq)
        {
            Z3Expr x = _z3Ctx.MkConst("x", eq.Domain[0]);
            Quantifier query = _z3Ctx.MkExists(new[] { x }, eq.Apply(x, BV(obj)));
            Trace.Assert(_fix.Query(query) == Status.SATISFIABLE);
            Z3Expr assignments = _fix.GetAnswer();
            if (!assignments.IsOr)
                return obj.ToString();

            string best = obj.ToString();
            foreach (Z3Expr fullAsg in assignments.Args)
            {
                Z3Expr asg = fullAsg.IsAnd ? fullAsg.Args[0] : fullAsg;
                uint val = ((BitVecNum)asg.Args[1]).UInt;
                if (_debugInfo.TryGetValue(val, out string? candidate) && candidate.Length < best.Length)
                    best = candidate;
            }

            return best;
        }

        private ModelCtx NewCtx(string? dbg)
        {
            uint id = NextId();
            AddFact(_ctx, id);
            var ctx = new ModelCtx(id);
            if (dbg != null)
                _debugInfo.Add(id, dbg);
            return WithDbg(ctx);
        }

        private CtxMorphism NewCtxMorph(ModelCtx from, ModelCtx to, string? dbg)
        {
            uint id = NextId();
            AddFact(_ctxMorph, from.Id, id, to.Id);
            var ctxMorph = new CtxMorphism(id, from, to);
            if (dbg != null)
                _debugInfo.Add(id, dbg);
            return WithDbg(ctxMorph);
        }

        private Ty NewTy(ModelCtx ctx, string? dbg)
        {
            uint id = NextId();
            AddFact(_ty, ctx.Id, id);
            var ty = new Ty(id, ctx);
            if (dbg != null)
                _debugInfo.Add(id, dbg);
            return WithDbg(ty);
        }

        private Tm NewTm(Ty ty, string? dbg)
        {
            uint id = NextId();
            AddFact(_tmTy, ty.Context.Id, id, ty.Id);
            var tm = new Tm(id, ty);
            if (dbg != null)
                _debugInfo.Add(id, dbg);
            return WithDbg(tm);
        }

        private bool IsTy(ModelCtx ctx, Ty ty)
            => _fix.Query((BoolExpr)_ty.Apply(BV(ctx), BV(ty))) == Status.SATISFIABLE;

        private bool IsTm(ModelCtx ctx, Tm tm, Ty ty)
            => _fix.Query((BoolExpr)_tmTy.Apply(BV(ctx), BV(tm), BV(ty))) == Status.SATISFIABLE;

        private bool IsCtxEq(ModelCtx ctx1, ModelCtx ctx2)
            => _fix.Query((BoolExpr)_ctxEq.Apply(BV(ctx1), BV(ctx2))) == Status.SATISFIABLE;

        private bool IsTyEq(Ty ty1, Ty ty2)
            => _fix.Query((BoolExpr)_tyEq.Apply(BV(ty1), BV(ty2))) == Status.SATISFIABLE;

        private bool IsTmEq(Tm tm1, Tm tm2)
            => _fix.Query((BoolExpr)_tmEq.Apply(BV(tm1), BV(tm2))) == Status.SATISFIABLE;

        private bool IsComprehension(Ty ty, ModelCtx ctx)
            => _fix.Query((BoolExpr)_comprehension.Apply(BV(ty.Context), BV(ty), BV(ctx))) == Status.SATISFIABLE;

        private bool IsId(Tm a, Tm b, Ty ty)
            => _fix.Query((BoolExpr)_id.Apply(BV(a), BV(b), BV(ty))) == Status.SATISFIABLE;

        private BitVecNum BV(ModelObject obj) => _z3Ctx.MkBV(obj.Id, SortSize);

        public ModelObject TypeCheck(Def def)
        {
            using (_ctxInfo.Remember())
            {
                foreach (CtxExt ctxExt in def.CtxExts)
                    ExtendContext(ctxExt);

                Ty retTy = TypeCheckType(def.RetTy);
                Tm body = TypeCheckTerm(def.Body, retTy);

                return body;
            }
        }

        private Ty ExtendContext(CtxExt ext)
        {
            Ty ty = TypeCheckType(ext.Type);
            _ctxInfo.Extend(ext.Name.IsDiscard ? null : ext.Name.Name, ty);
            // Put this term into the context because it might have equalities that we need.
            _ctxInfo.AccessLast();
            return ty;
        }

        private Ty TypeCheckType(Expr expr)
        {
            if (!(TypeCheck(expr) is Ty ty))
                throw new Exception($"{expr} is not a type");

            return ty;
        }

        private Tm TypeCheckAnyTerm(Expr expr)
        {
            if (!(TypeCheck(expr) is Tm tm))
                throw new Exception($"{expr} is not a term");

            return tm;
        }

        private Tm TypeCheckTerm(Expr expr, Ty ty)
        {
            Tm tm = TypeCheckAnyTerm(expr);
            if (!IsTyEq(ty, tm.Ty))
            {
                string msg =
                    $"Unexpected type of term.{Environment.NewLine}" +
                    $"Expected: {ShortestDbgString(ty)}{Environment.NewLine}" +
                    $"Actual: {ShortestDbgString(tm.Ty)}";
                throw new Exception(msg);
            }

            return tm;
        }

        private ModelObject TypeCheck(Expr expr)
        {
            switch (expr)
            {
                case IdExpr { Id: string id }:
                    if (id == "bool")
                        return FormBool(_ctxInfo.Ctx);
                    if (id == "true")
                        return IntroduceTrue(FormBool(_ctxInfo.Ctx));
                    if (id == "false")
                        return IntroduceFalse(FormBool(_ctxInfo.Ctx));
                    if (id == "nat")
                        return FormNat(_ctxInfo.Ctx);
                    if (id == "O")
                        return IntroduceZero(FormNat(_ctxInfo.Ctx));

                    return _ctxInfo.AccessVar(id);
                case LetExpr let:
                    using (_ctxInfo.Remember())
                    {
                        Ty ty = TypeCheckType(let.Type);
                        Tm tm = TypeCheckTerm(let.Val, ty);
                        if (!let.Name.IsDiscard)
                            _ctxInfo.Define(let.Name.Name, tm);
                        return TypeCheck(let.Body);
                    }
                case AppExpr { Fun: string fun, Args: var args }:
                    if (fun == "id" && args.Count == 2)
                    {
                        Tm a = TypeCheckAnyTerm(args[0]);
                        Tm b = TypeCheckTerm(args[1], a.Ty);
                        return FormId(a, b);
                    }
                    if (fun == "refl" && args.Count == 1)
                    {
                        Tm a = TypeCheckAnyTerm(args[0]);
                        return IntroduceRefl(a, FormId(a, a));
                    }
                    if (fun == "S")
                    {
                        Ty natInCurCtx = FormNat(_ctxInfo.Ctx);
                        Tm arg = TypeCheckTerm(args.Single(), natInCurCtx);

                        ModelCtx succCtx = Comprehension(_ctxInfo.Ctx, natInCurCtx, "pred");
                        Ty natInSuccCtx = FormNat(succCtx);
                        Tm succTm = IntroduceSucc(natInSuccCtx);

                        // Now we return succTm{<id, arg>}
                        CtxMorphism ext = TermBar(arg, succCtx);
                        Tm tmSubst = SubstTerm(succTm, ext, natInCurCtx);
                        return tmSubst;
                    }
                    if (fun == "dump")
                    {
                        ModelObject result = TypeCheck(args[1]);
                        DumpRels(((IdExpr)args[0]).Id);
                        return result;
                    }

                    goto default;
                case ElimExpr elim:
                    Tm discTm = TypeCheckAnyTerm(elim.Discriminee);
                    if (IsTyEq(discTm.Ty, FormBool(_ctxInfo.Ctx)))
                        return ElimBool(discTm, elim);
                    if (IsTyEq(discTm.Ty, FormNat(_ctxInfo.Ctx)))
                        return ElimNat(discTm, elim);

                    goto default;
                default:
                    throw new Exception("Unhandled: " + expr);
            }
        }

        private void DumpRels(string rels)
        {
            string[] relArr = rels == "all" ? _rels.Keys.ToArray() : new[] { rels };
            foreach (string rel in relArr)
            {
                _fix.Query(_rels[rel]);
                Z3Expr answer = _fix.GetAnswer();
                Console.WriteLine("------- {0} ({1} rows) -------", rel, answer.IsOr ? answer.Args.Length : answer.IsFalse ? 0 : 1);
                Console.Write(ToDebug(answer));
            }
        }

        private string ToDebug(Z3Expr expr)
        {
            if (expr.IsFalse)
                return "";

            string ans = expr.ToString();
            ans = _debugInfo.Aggregate(
                    ans,
                    (acc, kvp) => acc.Replace($"#x{kvp.Key:x8}", "'" + kvp.Value + "'"));
            return ans + Environment.NewLine;
        }

        private ModelCtx Comprehension(ModelCtx ctx, Ty ty, string? nameForDbg)
        {
            Debug.Assert(IsCtxEq(ctx, ty.Context));

            if (_fix.Query(_z3Ctx.MkExists(new[] { _G }, _comprehension.Apply(BV(ctx), BV(ty), _G))) == Status.SATISFIABLE)
                return WithDbg(new ModelCtx(ExtractAnswer(0)));

            string? ctxDbg = ctx.GetDebugInfo();
            string? tyDbg = ty.GetDebugInfo();
            string? dbg = null;
            if (ctxDbg != null && tyDbg != null)
            {
                if (nameForDbg == null)
                    nameForDbg = "_";

                if (ctxDbg != "")
                    dbg = $"{ctxDbg}, {nameForDbg} : {tyDbg}";
                else
                    dbg = $"{nameForDbg} : {tyDbg}";
            }

            ModelCtx newCtx = NewCtx(dbg);
            AddFact(_comprehension, ctx.Id, ty.Id, newCtx.Id);
            return newCtx;
        }

        private Ty FormId(Tm a, Tm b)
        {
            Debug.Assert(IsTyEq(a.Ty, b.Ty));

            Quantifier query =
                _z3Ctx.MkExists(
                    new[] { _s },
                    (BoolExpr)_id.Apply(BV(a), BV(b), _s));
            if (_fix.Query(query) == Status.SATISFIABLE)
                return WithDbg(new Ty(ExtractAnswer(0), a.Context));

            string? aDbg = a.GetDebugInfo();
            string? bDbg = b.GetDebugInfo();
            string? dbg = aDbg != null && bDbg != null ? $"Id({aDbg}, {bDbg})" : null;
            Ty id = NewTy(a.Context, dbg);
            AddFact(_id, a.Id, b.Id, id.Id);
            return id;
        }

        private Tm IntroduceRefl(Tm a, Ty idTy)
        {
            Debug.Assert(IsId(a, a, idTy));

            Quantifier query =
                _z3Ctx.MkExists(
                    new[] { _M },
                    (BoolExpr)_refl.Apply(_M) &
                    (BoolExpr)_tmTy.Apply(BV(a.Context), _M, BV(idTy)));
            if (_fix.Query(query) == Status.SATISFIABLE)
                return WithDbg(new Tm(ExtractAnswer(0), idTy));

            string? aDbg = a.GetDebugInfo();
            string? dbg = aDbg != null ? $"Refl({aDbg})" : null;
            Tm refl = NewTm(idTy, dbg);
            AddFact(_refl, refl.Id);
            return refl;
        }

        private Ty FormBool(ModelCtx ctx)
        {
            Quantifier query =
                _z3Ctx.MkExists(
                    new[] { _s },
                    (BoolExpr)_bool.Apply(_s) &
                    (BoolExpr)_ty.Apply(BV(ctx), _s));
            if (_fix.Query(query) == Status.SATISFIABLE)
                return WithDbg(new Ty(ExtractAnswer(0), ctx));

            string? ctxDbg = ctx.GetDebugInfo();
            Ty @bool = NewTy(ctx, $"bool({ctxDbg})");
            AddFact(_bool, @bool.Id);
            return @bool;
        }

        private Ty FormNat(ModelCtx ctx)
        {
            Quantifier query =
                _z3Ctx.MkExists(
                    new[] { _s },
                    (BoolExpr)_nat.Apply(_s) &
                    (BoolExpr)_ty.Apply(BV(ctx), _s));
            if (_fix.Query(query) == Status.SATISFIABLE)
                return WithDbg(new Ty(ExtractAnswer(0), ctx));

            string? ctxDbg = ctx.GetDebugInfo();
            Ty nat = NewTy(ctx, $"nat({ctxDbg})");
            AddFact(_nat, nat.Id);
            return nat;
        }

        private Tm IntroduceTrue(Ty @bool)
        {
            Quantifier query =
                _z3Ctx.MkExists(
                    new[] { _M },
                    (BoolExpr)_true.Apply(_M) &
                    (BoolExpr)_tmTy.Apply(BV(@bool.Context), _M, BV(@bool)));
            if (_fix.Query(query) == Status.SATISFIABLE)
                return WithDbg(new Tm(ExtractAnswer(0), @bool));

            string? ctxDbg = @bool.Context.GetDebugInfo();
            string? dbg = ctxDbg != null ? $"true({ctxDbg})" : null;
            Tm @true = NewTm(@bool, dbg);
            AddFact(_true, @true.Id);
            return @true;
        }

        private Tm IntroduceFalse(Ty @bool)
        {
            Quantifier query =
                _z3Ctx.MkExists(
                    new[] { _M },
                    (BoolExpr)_false.Apply(_M) &
                    (BoolExpr)_tmTy.Apply(BV(@bool.Context), _M, BV(@bool)));
            if (_fix.Query(query) == Status.SATISFIABLE)
                return WithDbg(new Tm(ExtractAnswer(0), @bool));

            string? ctxDbg = @bool.Context.GetDebugInfo();
            string? dbg = ctxDbg != null ? $"false({ctxDbg})" : null;
            Tm @false = NewTm(@bool, dbg);
            AddFact(_false, @false.Id);
            return @false;
        }

        private uint ExtractAnswer(int varIndex)
        {
            Z3Expr expr = _fix.GetAnswer();
            if (expr.IsOr)
                expr = expr.Args[0];

            if (expr.IsAnd)
                expr = expr.Args[varIndex];
            else
                Debug.Assert(varIndex == 0);

            Debug.Assert(expr.IsEq);
            return ((BitVecNum)expr.Args[1]).UInt;
        }

        private Tm IntroduceZero(Ty nat)
        {
            Quantifier query =
                _z3Ctx.MkExists(
                    new[] { _M },
                    (BoolExpr)_zero.Apply(_M) &
                    (BoolExpr)_tmTy.Apply(BV(nat.Context), _M, BV(nat)));
            if (_fix.Query(query) == Status.SATISFIABLE)
                return WithDbg(new Tm(ExtractAnswer(0), nat));

            string? ctxDbg = nat.Context.GetDebugInfo();
            string? dbg = ctxDbg != null ? $"0({ctxDbg})" : null;
            Tm zero = NewTm(nat, dbg);
            AddFact(_zero, zero.Id);
            return zero;
        }

        // Introduce successor term of type nat in context of that nat type.
        // The passed nat type should be a type in a context G, x : nat.
        private Tm IntroduceSucc(Ty nat)
        {
            Debug.Assert(
                _fix.Query(
                    _z3Ctx.MkExists(
                        new[] { _G, _s },
                        (BoolExpr)_nat.Apply(BV(nat)) &
                        (BoolExpr)_comprehension.Apply(_G, _s, BV(nat.Context)) &
                        (BoolExpr)_nat.Apply(_s))) == Status.SATISFIABLE);

            var query =
                _z3Ctx.MkExists(
                    new[] { _M, _G },
                    (BoolExpr)_succ.Apply(_M) &
                    (BoolExpr)_tmTy.Apply(_G, _M, BV(nat)));
            if (_fix.Query(query) == Status.SATISFIABLE)
                return WithDbg(new Tm(ExtractAnswer(0), nat));

            Tm succ = NewTm(nat, "succ");
            AddFact(_succ, succ.Id);
            return succ;
        }

        // Given G |- tm : ty, make <id, tm> : G -> G.ty
        private CtxMorphism TermBar(Tm tm, ModelCtx ctxTo)
        {
            Debug.Assert(IsComprehension(tm.Ty, ctxTo));
            CtxMorphism idMorph = IdMorph(tm.Context);
            CtxMorphism ext = Extension(idMorph, tm, ctxTo);
            return ext;
        }

        // Given f : D -> G and G |- s type, construct
        // wk f : D.s{f} -> G.s as <f . p1(s{f}), p2(s{f})>
        private CtxMorphism Weaken(CtxMorphism morphism, Ty ty)
        {
            Debug.Assert(IsCtxEq(morphism.To, ty.Context));

            // s{f}
            Ty substTy = SubstType(ty, morphism);

            // D.s{f}
            ModelCtx ctxFrom = Comprehension(morphism.From, substTy, null);

            // G.s
            ModelCtx ctxTo = Comprehension(morphism.To, ty, null);

            // p1(s{f}) : D.s{f} -> D
            CtxMorphism projCtx = ProjCtx(ctxFrom, substTy);

            // D.s{f} |- s{f} type
            Ty substTyInCtxFrom = SubstType(substTy, projCtx);
            // D.s{f} |- p2(s{f}) : s{f}
            Tm projTm = ProjTm(substTy, substTyInCtxFrom);

            CtxMorphism comp = Compose(morphism, projCtx);
            return Extension(comp, projTm, ctxTo);
        }

        private CtxMorphism ProjCtx(ModelCtx fromCtx, Ty removedTy)
        {
            Debug.Assert(IsComprehension(removedTy, fromCtx));

            if (_fix.Query(_z3Ctx.MkExists(new[] { _f }, _projCtx.Apply(BV(removedTy.Context), BV(removedTy), _f))) == Status.SATISFIABLE)
                return WithDbg(new CtxMorphism(ExtractAnswer(0), fromCtx, removedTy.Context));

            string? fromCtxDbg = fromCtx.GetDebugInfo();
            string? dbg = fromCtxDbg != null ? $"p1({fromCtxDbg})" : null;
            CtxMorphism ctxMorphism = NewCtxMorph(fromCtx, removedTy.Context, dbg);
            AddFact(_projCtx, removedTy.Context.Id, removedTy.Id, ctxMorphism.Id);
            return ctxMorphism;
        }

        private Tm ProjTm(Ty addedVarTy, Ty fullTy)
        {
            if (_fix.Query(_z3Ctx.MkExists(new[] { _M }, _projTm.Apply(BV(addedVarTy.Context), BV(addedVarTy), _M))) == Status.SATISFIABLE)
                return WithDbg(new Tm(ExtractAnswer(0), fullTy));

            string? ctxDbg = fullTy.Context.GetDebugInfo();
            string? dbg = ctxDbg != null ? $"p2({ctxDbg})" : null;

            Tm tm = NewTm(fullTy, dbg);
            AddFact(_projTm, addedVarTy.Context.Id, addedVarTy.Id, tm.Id);
            return tm;
        }

        private Tm ElimBool(Tm discriminee, ElimExpr elim)
        {
            if (elim.IntoExts.Count != 1)
                throw new Exception($"Invalid context extension {string.Join(" ", elim.IntoExts)}");

            if (elim.Cases.Count != 2)
                throw new Exception($"Expected 2 cases for nat elimination");

            if (elim.Cases[0].CaseExts.Count != 0)
                throw new Exception($"{elim.Cases[0]}: expected no context extensions");

            if (elim.Cases[1].CaseExts.Count != 0)
                throw new Exception($"{elim.Cases[1]}: expected no context extensions");

            Ty boolInElimCtx = FormBool(_ctxInfo.Ctx);
            Ty intoTy;
            using (_ctxInfo.Remember())
            {
                Ty extTy = ExtendContext(elim.IntoExts[0]);
                if (!IsTyEq(extTy, boolInElimCtx))
                {
                    string? intoExtTyDbg = extTy.GetDebugInfo();
                    string dbg = intoExtTyDbg != null ? $"Expected extension by bool, got extension by {intoExtTyDbg}" : "Expected extension by bool";
                    throw new Exception(dbg);
                }

                intoTy = TypeCheckType(elim.IntoTy);
            }

            Tm @true = IntroduceTrue(boolInElimCtx);
            Ty expectedTyTrueCase = SubstType(intoTy, TermBar(@true, intoTy.Context));
            Tm trueCase = TypeCheckTerm(elim.Cases[0].Body, expectedTyTrueCase);

            Tm @false = IntroduceFalse(boolInElimCtx);
            Ty expectedTyFalseCase = SubstType(intoTy, TermBar(@false, intoTy.Context));
            Tm falseCase = TypeCheckTerm(elim.Cases[1].Body, expectedTyFalseCase);

            Tm elimTm = NewTm(intoTy, "elimb");
            AddFact(_boolElim, trueCase.Id, falseCase.Id, elimTm.Id);

            CtxMorphism addDisc = TermBar(discriminee, intoTy.Context);
            Tm substTm = SubstTermAndType(elimTm, addDisc);
            return substTm;
        }

        private Tm ElimNat(Tm discriminee, ElimExpr elim)
        {
            if (elim.IntoExts.Count != 1)
                throw new Exception($"Invalid context extension {string.Join(" ", elim.IntoExts)}");

            if (elim.Cases.Count != 2)
                throw new Exception($"Expected 2 cases for nat elimination");

            if (elim.Cases[0].CaseExts.Count != 0)
                throw new Exception($"{elim.Cases[0]}: expected no context extensions");

            if (elim.Cases[1].CaseExts.Count != 2)
                throw new Exception($"{elim.Cases[1]}: expected 2 context extensions");

            Ty natInElimCtx = FormNat(_ctxInfo.Ctx);
            Ty intoTy;
            using (_ctxInfo.Remember())
            {
                Ty extTy = ExtendContext(elim.IntoExts[0]);
                if (!IsTyEq(extTy, natInElimCtx))
                {
                    string? intoExtTyDbg = extTy.GetDebugInfo();
                    string dbg = intoExtTyDbg != null ? $"Expected extension by nat, got extension by {intoExtTyDbg}" : "Expected extension by nat";
                    throw new Exception(dbg);
                }

                intoTy = TypeCheckType(elim.IntoTy);
            }

            Tm zero = IntroduceZero(natInElimCtx);
            Ty expectedTy = SubstType(intoTy, TermBar(zero, intoTy.Context));
            Tm zeroCase = TypeCheckTerm(elim.Cases[0].Body, expectedTy);
            Tm succCase;

            using (_ctxInfo.Remember())
            {
                Ty predTy = ExtendContext(elim.Cases[1].CaseExts[0]);
                if (!IsTyEq(predTy, natInElimCtx))
                {
                    string? predTyDbg = predTy.GetDebugInfo();
                    string dbg = predTyDbg != null ? $"Expected extension by nat, got extension by {predTyDbg}" : "Expected extension by nat";
                    throw new Exception(dbg);
                }

                Ty ihTy = ExtendContext(elim.Cases[1].CaseExts[1]);
                if (!IsTyEq(ihTy, intoTy))
                {
                    string? ihTyDbg = ihTy.GetDebugInfo();
                    string? intoTyDbg = intoTy.GetDebugInfo();
                    string dbg =
                        ihTyDbg != null && intoTyDbg != null
                        ? $"Expected extension by {intoTyDbg}, got extension by {intoTy}"
                        : "Invalid extension in successor case";
                    throw new Exception(dbg);
                }

                // We need to make intoTy[suc(n)/n] in this context.
                // First project away the IH
                CtxMorphism projectIH = ProjCtx(_ctxInfo.Ctx, ihTy);

                // Now add the successor of the predecessor, giving a context that ends with two nats
                Ty natInPredCtx = FormNat(ihTy.Context);
                Tm succOfPred = IntroduceSucc(natInPredCtx);
                ModelCtx ctxWithSucc = Comprehension(ihTy.Context, natInPredCtx, "succ");
                CtxMorphism addSuccOfPred = TermBar(succOfPred, ctxWithSucc);

                // Now make the morphism that removes not the last, but second to last nat, i.e.
                // f : G, pred : nat, succ : nat -> G, succ : nat
                CtxMorphism projectPred = ProjCtx(ihTy.Context, predTy);
                CtxMorphism removePred = Weaken(projectPred, natInElimCtx);

                // Finally apply these morphisms.
                Ty intoTy1 = SubstType(intoTy, removePred);
                Ty intoTy2 = SubstType(intoTy1, addSuccOfPred);
                Ty intoTy3 = SubstType(intoTy2, projectIH);
                Debug.Assert(IsCtxEq(intoTy3.Context, _ctxInfo.Ctx));

                succCase = TypeCheckTerm(elim.Cases[1].Body, intoTy3);
            }

            Tm elimTm = NewTm(intoTy, "elim");
            AddFact(_natElim, zeroCase.Id, succCase.Id, elimTm.Id);

            var addIH = TermBar(elimTm, Comprehension(elimTm.Context, intoTy, null));
            Tm right = SubstTermAndType(succCase, addIH);

            CtxMorphism addDisc = TermBar(discriminee, intoTy.Context);
            Tm substTm = SubstTermAndType(elimTm, addDisc);
            //Trace.Assert(IsTmEq(substTm, IntroduceZero(FormNat(substTm.Context))));
            return substTm;
        }

        private CtxMorphism IdMorph(ModelCtx ctx)
        {
            Quantifier query =
                _z3Ctx.MkExists(
                    new[] { _f, },
                    (BoolExpr)_idMorph.Apply(_f) &
                    (BoolExpr)_ctxMorph.Apply(BV(ctx), _f, BV(ctx)));

            if (_fix.Query(query) == Status.SATISFIABLE)
                return WithDbg(new CtxMorphism(ExtractAnswer(0), ctx, ctx));

            string? ctxDbg = ctx.GetDebugInfo();
            string? dbg = ctxDbg != null ? $"id({ctxDbg})" : null;

            CtxMorphism ctxMorphism = NewCtxMorph(ctx, ctx, dbg);
            AddFact(_idMorph, ctxMorphism.Id);
            return ctxMorphism;
        }

        private CtxMorphism Compose(CtxMorphism g, CtxMorphism f)
        {
            Debug.Assert(IsCtxEq(f.To, g.From));

            Quantifier query =
                _z3Ctx.MkExists(
                    new[] { _f },
                    _comp.Apply(BV(g), BV(f), _f));

            if (_fix.Query(query) == Status.SATISFIABLE)
                return WithDbg(new CtxMorphism(ExtractAnswer(0), f.From, g.To));

            string? gDbg = g.GetDebugInfo();
            string? fDbg = f.GetDebugInfo();
            string? dbg = gDbg != null && fDbg != null ? $"{gDbg} . {fDbg}" : null;
            CtxMorphism gf = NewCtxMorph(f.From, g.To, dbg);
            AddFact(_comp, g.Id, f.Id, gf.Id);
            return gf;
        }

        private CtxMorphism Extension(CtxMorphism morphism, Tm tm, ModelCtx ctxTo)
        {
            Debug.Assert(IsCtxEq(morphism.From, tm.Context));

            Quantifier query =
                _z3Ctx.MkExists(
                    new[] { _f },
                    _extension.Apply(
                        BV(morphism),
                        BV(tm),
                        _f));

            if (_fix.Query(query) == Status.SATISFIABLE)
                return WithDbg(new CtxMorphism(ExtractAnswer(0), morphism.From, ctxTo));

            string? morphismDbg = morphism.GetDebugInfo();
            string? tmDbg = tm.GetDebugInfo();
            string? dbg = morphismDbg != null && tmDbg != null ? $"<{morphismDbg}, {tmDbg}>" : null;

            CtxMorphism newMorphism = NewCtxMorph(morphism.From, ctxTo, dbg);
            AddFact(_extension, morphism.Id, tm.Id, newMorphism.Id);
            return newMorphism;
        }

        private Ty SubstType(Ty oldTy, CtxMorphism morphism)
        {
            Debug.Assert(IsCtxEq(oldTy.Context, morphism.To));

            if (_fix.Query(_z3Ctx.MkExists(new[] { _s }, _tySubst.Apply(BV(oldTy), BV(morphism), _s))) == Status.SATISFIABLE)
                return WithDbg(new Ty(ExtractAnswer(0), morphism.From));

            string? tyDbg = oldTy.GetDebugInfo();
            string? ctxMorphDbg = morphism.GetDebugInfo();
            string? dbg = ctxMorphDbg != null && tyDbg != null ? $"{tyDbg}{{{ctxMorphDbg}}}" : null;

            Ty newTy = NewTy(morphism.From, dbg);
            AddFact(_tySubst, oldTy.Id, morphism.Id, newTy.Id);
            return newTy;
        }

        private Tm SubstTerm(Tm oldTm, CtxMorphism morphism, Ty newTy)
        {
            Debug.Assert(IsCtxEq(oldTm.Context, morphism.To));
            Debug.Assert(IsCtxEq(morphism.From, newTy.Context));

            if (_fix.Query(_z3Ctx.MkExists(new[] { _M }, _tmSubst.Apply(BV(oldTm), BV(morphism), _M))) == Status.SATISFIABLE)
                return WithDbg(new Tm(ExtractAnswer(0), newTy));

            string? ctxMorphDbg = morphism.GetDebugInfo();
            string? tmDbg = oldTm.GetDebugInfo();
            string? dbg = ctxMorphDbg != null && tmDbg != null ? $"{tmDbg}{{{ctxMorphDbg}}}" : null;

            Tm tm = NewTm(newTy, dbg);
            AddFact(_tmSubst, oldTm.Id, morphism.Id, tm.Id);
            return tm;
        }

        private Tm SubstTermAndType(Tm oldTm, CtxMorphism morphism)
        {
            Ty newTy = SubstType(oldTm.Ty, morphism);
            return SubstTerm(oldTm, morphism, newTy);
        }

        private void AddFact(FuncDecl pred, params uint[] args)
        {
            _fix.AddFact(pred, args);
            Verify();
        }

        [Conditional("DEBUG")]
        private void Verify()
        {
            Quantifier typesOfEqTerms = _z3Ctx.MkExists(
                new[] { _M, _N, _G, _D, _s, _t },
                (BoolExpr)_tmEq.Apply(_M, _N) &
                (BoolExpr)_tmTy.Apply(_G, _M, _s) &
                (BoolExpr)_tmTy.Apply(_D, _N, _t) &
                (!(BoolExpr)_tyEq.Apply(_s, _t) |
                 !(BoolExpr)_ctxEq.Apply(_G, _D)));

            if (_fix.Query(typesOfEqTerms) != Status.UNSATISFIABLE)
                throw new Exception("Verification has failed:" + Environment.NewLine + ToDebug(_fix.GetAnswer()));

            Quantifier typesOfEqTypes = _z3Ctx.MkExists(
                new[] { _G, _D, _s, _t },
                (BoolExpr)_tyEq.Apply(_s, _t) &
                (BoolExpr)_ty.Apply(_G, _s) &
                (BoolExpr)_ty.Apply(_D, _t) &
                 !(BoolExpr)_ctxEq.Apply(_G, _D));

            if (_fix.Query(typesOfEqTypes) != Status.UNSATISFIABLE)
                throw new Exception("Verification has failed:" + Environment.NewLine + ToDebug(_fix.GetAnswer()));

            Quantifier compositions = _z3Ctx.MkExists(
                new[] { _g, _f, _gf, _A, _B, _C, _D, _E, _F, },
                (BoolExpr)_comp.Apply(_g, _f, _gf) &
                (BoolExpr)_ctxMorph.Apply(_A, _f, _B) &
                (BoolExpr)_ctxMorph.Apply(_C, _g, _D) &
                (BoolExpr)_ctxMorph.Apply(_E, _gf, _F) &
                (!(BoolExpr)_ctxEq.Apply(_B, _C) |
                 !(BoolExpr)_ctxEq.Apply(_E, _A) |
                 !(BoolExpr)_ctxEq.Apply(_F, _D)));

            if (_fix.Query(compositions) != Status.UNSATISFIABLE)
                throw new Exception("Verification has failed:" + Environment.NewLine + ToDebug(_fix.GetAnswer()));

            Quantifier idMorphs = _z3Ctx.MkExists(
                new[] { _f, _G, _D },
                (BoolExpr)_idMorph.Apply(_f) &
                (BoolExpr)_ctxMorph.Apply(_G, _f, _D) &
                 !(BoolExpr)_ctxEq.Apply(_G, _D));

            if (_fix.Query(idMorphs) != Status.UNSATISFIABLE)
                throw new Exception("Verification has failed:" + Environment.NewLine + ToDebug(_fix.GetAnswer()));

            Quantifier tySubsts = _z3Ctx.MkExists(
                new[] { _s, _t, _G, _D, _f, _A, _B },
                (BoolExpr)_tySubst.Apply(_s, _f, _t) &
                (BoolExpr)_ty.Apply(_G, _s) &
                (BoolExpr)_ty.Apply(_D, _t) &
                (BoolExpr)_ctxMorph.Apply(_A, _f, _B) &
                (!(BoolExpr)_ctxEq.Apply(_B, _G) |
                 !(BoolExpr)_ctxEq.Apply(_A, _D)));

            if (_fix.Query(tySubsts) != Status.UNSATISFIABLE)
                throw new Exception("Verification has failed:" + Environment.NewLine + ToDebug(_fix.GetAnswer()));

            Quantifier tmSubsts = _z3Ctx.MkExists(
                new[] { _M, _N, _G, _D, _s, _t, _f, _A, _B },
                (BoolExpr)_tmSubst.Apply(_M, _f, _N) &
                (BoolExpr)_tmTy.Apply(_G, _M, _s) &
                (BoolExpr)_tmTy.Apply(_D, _N, _t) &
                (BoolExpr)_ctxMorph.Apply(_A, _f, _B) &
                (!(BoolExpr)_ctxEq.Apply(_B, _G) |
                 !(BoolExpr)_ctxEq.Apply(_A, _D)));

            if (_fix.Query(tmSubsts) != Status.UNSATISFIABLE)
                throw new Exception("Verification has failed:" + Environment.NewLine + ToDebug(_fix.GetAnswer()));

            Quantifier projCtxs = _z3Ctx.MkExists(
                new[] { _G, _s, _f, _A, _B },
                (BoolExpr)_projCtx.Apply(_G, _s, _f) &
                (BoolExpr)_ctxMorph.Apply(_A, _f, _B) &
                (!(BoolExpr)_ctxEq.Apply(_B, _G) |
                 !(BoolExpr)_comprehension.Apply(_G, _s, _A)));

            if (_fix.Query(projCtxs) != Status.UNSATISFIABLE)
                throw new Exception("Verification has failed:" + Environment.NewLine + ToDebug(_fix.GetAnswer()));

            Quantifier projTms = _z3Ctx.MkExists(
                new[] { _G, _s, _M, _D, _t },
                (BoolExpr)_projTm.Apply(_G, _s, _M) &
                (BoolExpr)_tmTy.Apply(_D, _M, _t) &
                (!(BoolExpr)_comprehension.Apply(_G, _s, _D)));

            if (_fix.Query(projTms) != Status.UNSATISFIABLE)
                throw new Exception("Verification has failed:" + Environment.NewLine + ToDebug(_fix.GetAnswer()));

            Quantifier extensions = _z3Ctx.MkExists(
                new[] { _f, _M, _g, _G, _D, _A, _B, _C, _s, _t },
                (BoolExpr)_extension.Apply(_f, _M, _g) &
                (BoolExpr)_ctxMorph.Apply(_G, _f, _D) &
                (BoolExpr)_tmTy.Apply(_G, _M, _s) &
                (BoolExpr)_tySubst.Apply(_s, _f, _t) &
                (BoolExpr)_ctxMorph.Apply(_A, _g, _B) &
                (!(BoolExpr)_ctxEq.Apply(_A, _G) |
                 !(BoolExpr)_comprehension.Apply(_D, _t, _B)));

            if (_fix.Query(extensions) != Status.UNSATISFIABLE)
                throw new Exception("Verification has failed:" + Environment.NewLine + ToDebug(_fix.GetAnswer()));
        }

        public void Dispose()
        {
            _z3Ctx.Dispose();
        }

        private class ContextInfo
        {
            private readonly TypeChecker _tc;

            private readonly List<(string? name, ModelObject obj)> _vars = new List<(string? name, ModelObject obj)>();

            public ContextInfo(TypeChecker tc, ModelCtx initialCtx)
            {
                _tc = tc;
                Ctx = initialCtx;
            }

            public int NumVars => _vars.Count;

            public ModelCtx Ctx { get; private set; }

            // Extend the context with a term of the specified type.
            public void Extend(string? name, Ty ty)
            {
                Debug.Assert(_tc.IsCtxEq(ty.Context, Ctx));

                ModelCtx newCtx = _tc.Comprehension(Ctx, ty, name);
                _vars.Add((name, ty));
                Ctx = newCtx;
            }

            // Define a term in the current context.
            public void Define(string name, Tm tm)
            {
                Debug.Assert(_tc.IsCtxEq(tm.Context, Ctx));
                _vars.Add((name, tm));
            }

            // Construct a term that accesses the var by the specified name.
            public Tm AccessVar(string name)
            {
                int index = _vars.FindLastIndex(t => t.name == name);
                if (index == -1)
                    throw new ArgumentException($"No variable exists by name {name}", nameof(name));

                return Access(index);
            }

            public Tm AccessLast()
            {
                if (_vars.Count <= 0)
                    throw new InvalidOperationException("No variables have been added to the context");

                return Access(_vars.Count - 1);
            }

            private Tm Access(int index)
            {
                return Go(_vars.Count - 1, Ctx);

                Tm Go(int i, ModelCtx nextCtx)
                {
                    (string? name, ModelObject obj) = _vars[i];
                    // Make context morphism that gets us from nextCtx to ty's ctx by projecting out added variable.

                    if (i == index)
                    {
                        if (obj is Tm tm)
                            return tm;

                        Ty ty = (Ty)obj;
                        CtxMorphism ctxProj = _tc.ProjCtx(nextCtx, ty);
                        // addedTy is in ctx, and we want it in nextCtx, so
                        // make addedTy{ctxProj} = tySubst in nextCtx.
                        Ty tySubst = _tc.SubstType(ty, ctxProj);

                        Tm tmProj = _tc.ProjTm(ty, tySubst);
                        return tmProj;
                    }
                    else
                    {
                        if (obj is Tm)
                        {
                            // Skip definition that does not extend context
                            return Go(i - 1, nextCtx);
                        }

                        Ty ty = (Ty)obj;
                        Tm tm = Go(i - 1, ty.Context);
                        // nextCtx = ctx, x : ty[in ctx]
                        // tm is term that accesses variable in ty's ctx
                        // ty is type of variable in ctx

                        Debug.Assert(_tc.IsComprehension(ty, nextCtx));
                        Debug.Assert(_tc.IsCtxEq(tm.Context, ty.Context));

                        CtxMorphism ctxProj = _tc.ProjCtx(nextCtx, ty);
                        Tm tmSubst = _tc.SubstTermAndType(tm, ctxProj);
                        return tmSubst;
                    }
                }
            }

            public ContextSavePoint Remember()
                => new ContextSavePoint(this);

            public struct ContextSavePoint : IDisposable
            {
                private readonly ContextInfo _ctx;
                private readonly int _numVars;
                private readonly ModelCtx _modelCtx;
                public ContextSavePoint(ContextInfo ctx)
                {
                    _ctx = ctx;
                    _numVars = ctx._vars.Count;
                    _modelCtx = ctx.Ctx;
                }

                public void Dispose()
                {
                    Debug.Assert(_ctx._vars.Count >= _numVars);

                    _ctx._vars.RemoveRange(_numVars, _ctx._vars.Count - _numVars);
                    _ctx.Ctx = _modelCtx;
                }
            }
        }

        private static readonly string s_z3Setup = @"
(define-sort CtxS () (_ BitVec {SortSize}))
(define-sort CtxMorphS () (_ BitVec {SortSize}))
(define-sort TyS () (_ BitVec {SortSize}))
(define-sort TmS () (_ BitVec {SortSize}))

; CtxEq G D -- |- G = D ctx
(declare-rel CtxEq (CtxS CtxS))
; CtxMorphEq f g -- G |- f = g => D
(declare-rel CtxMorphEq (CtxMorphS CtxMorphS))
; TyEq s t -- G |- s = t type
(declare-rel TyEq (TyS TyS))
; TmEq M N -- G |- M = N : s
(declare-rel TmEq (TmS TmS))

; Ctx G -- |- G ctx
(declare-rel Ctx (CtxS))
; CtxMorph G f D -- G |- f => D
(declare-rel CtxMorph (CtxS CtxMorphS CtxS))
; Ty G s -- G |- s type
(declare-rel Ty (CtxS TyS))
; TmTy G M s -- G |- M : s
(declare-rel TmTy (CtxS TmS TyS))

; Functional relations
; IdMorph f -- f is an identity context morphism
(declare-rel IdMorph (CtxMorphS))
; Comp g f h -- h is g . f
(declare-rel Comp (CtxMorphS CtxMorphS CtxMorphS))
; TySubst s f t -- t is s{f}
(declare-rel TySubst (TyS CtxMorphS TyS))
; TmSubst M f N -- N is M{f}
(declare-rel TmSubst (TmS CtxMorphS TmS))
; CtxEmpty G -- G is the empty (terminal) context
(declare-rel CtxEmpty (CtxS))
; Comprehension G s D -- |- G, x : s = D ctx
(declare-rel Comprehension (CtxS TyS CtxS))
; ProjCtx G s f -- f is the projection G, x : s |- p(s) => G
(declare-rel ProjCtx (CtxS TyS CtxMorphS))
; ProjTm G s M -- M is the projection G, x : s |- x : s
(declare-rel ProjTm (CtxS TyS TmS))
; Extension f M g -- g = 〈f, M〉
(declare-rel Extension (CtxMorphS TmS CtxMorphS))

; Intermediate relations
(declare-rel TmBar (TmS CtxMorphS))
(declare-rel Weakening (CtxMorphS TyS CtxMorphS))

; Type forming/introduction/elimination
(declare-rel Id (TmS TmS TyS))
(declare-rel Refl (TmS))

(declare-rel Bool (TyS))
(declare-rel True (TmS))
(declare-rel False (TmS))
(declare-rel BoolElim (TmS TmS TmS))

(declare-rel Nat (TyS))
(declare-rel Zero (TmS))
; Succ M -- M is successor term (in a context that ends with a nat -- the predecessor)
(declare-rel Succ (TmS))
; NatElim M N O -- O is nat elimination with zero-case M and successor-case N
(declare-rel NatElim (TmS TmS TmS))

(declare-var A CtxS)
(declare-var B CtxS)
(declare-var C CtxS)
(declare-var D CtxS)
(declare-var E CtxS)
(declare-var F CtxS)
(declare-var G CtxS)

(declare-var e CtxMorphS)
(declare-var f CtxMorphS)
(declare-var g CtxMorphS)
(declare-var h CtxMorphS)
(declare-var i CtxMorphS)
(declare-var j CtxMorphS)
(declare-var k CtxMorphS)
(declare-var l CtxMorphS)
(declare-var p CtxMorphS)
(declare-var q CtxMorphS)
(declare-var gf CtxMorphS)
(declare-var hg CtxMorphS)
(declare-var hgf CtxMorphS)

(declare-var r TyS)
(declare-var s TyS)
(declare-var t TyS)
(declare-var u TyS)
(declare-var v TyS)
(declare-var x TyS)

(declare-var M TmS)
(declare-var N TmS)
(declare-var O TmS)
(declare-var P TmS)
(declare-var Q TmS)
(declare-var R TmS)
(declare-var S TmS)
(declare-var T TmS)
(declare-var U TmS)

;;;;;;;;;; Equalities ;;;;;;;;;;

; CtxEq is an equivalence relation
(rule (=> (Ctx G) (CtxEq G G)) CtxEq-Reflexive)
(rule (=> (CtxEq G D) (CtxEq D G)) CtxEq-Symmetric)
(rule (=> (and (CtxEq G D) (CtxEq D B)) (CtxEq G B)) CtxEq-Transitive)

; CtxMorphEq is an equivalence relation
(rule (=> (CtxMorph G f D) (CtxMorphEq f f)) CtxMorphEq-Reflexive)
(rule (=> (CtxMorphEq f g) (CtxMorphEq g f)) CtxMorphEq-Symmetric)
(rule (=> (and (CtxMorphEq f g)
               (CtxMorphEq g h))
          (CtxMorphEq f h))
      CtxMorphEq-Transitive)

; TyEq is an equivalence relation
(rule (=> (Ty G s) (TyEq s s)) TyEq-Reflexive)
(rule (=> (TyEq s t) (TyEq t s)) TyEq-Symmetric)
(rule (=> (and (TyEq s t) (TyEq t r)) (TyEq s r)) TyEq-Transitive)

; TmEq is an equivalence relation
(rule (=> (TmTy G M s) (TmEq M M)) TmEq-Reflexive)
(rule (=> (TmEq M N) (TmEq N M)) TmEq-Symmetric)
(rule (=> (and (TmEq M N) (TmEq N O)) (TmEq M O)) TmEq-Transitive)

;;;;;;;;;; Congruence rules ;;;;;;;;;;

; Ctx
(rule (=> (and (Ctx G)
               (CtxEq G D))
          (Ctx D))
      Ctx-Congr)

; CtxMorph
(rule (=> (and (CtxMorph G f D)
               (CtxEq G A)
               (CtxMorphEq f g)
               (CtxEq D B))
          (CtxMorph A g B))
      CtxMorph-Congr)

; Comp
(rule (=> (and (Comp f g h)
               (CtxMorphEq f i)
               (CtxMorphEq g j)
               (CtxMorphEq h k))
          (Comp i j k))
      Comp-Congr)

; Ty
(rule (=> (and (Ty G s)
               (CtxEq G D)
               (TyEq s t))
          (Ty D t))
      Ty-Conv)

; TmTy
(rule (=> (and (TmTy G M s)
               (CtxEq G D)
               (TmEq M N)
               (TyEq s t))
          (TmTy D N t))
      Tm-Conv)

; IdMorph
(rule (=> (and (IdMorph f)
               (CtxMorphEq f g))
          (IdMorph g))
      IdMorph-Congr)

; TySubst
(rule (=> (and (TySubst s f t)
               (TyEq s u)
               (CtxMorphEq f g)
               (CtxMorphEq t v))
          (TySubst u g v))
      TySubst-Congr)

; TmSubst
(rule (=> (and (TmSubst M f N)
               (TmEq M O)
               (CtxMorphEq f g)
               (TmEq N P))
          (TmSubst O g P))
      TmSubst-Congr)

; CtxEmpty
(rule (=> (and (CtxEmpty G)
               (CtxEq G D))
          (CtxEmpty D))
      CtxEmpty-Congr)

; Comprehension
(rule (=> (and (Comprehension G s A)
               (CtxEq G D)
               (TyEq s t)
               (CtxEq A B))
          (Comprehension D t B))
      Comprehension-Congr)

; ProjCtx
(rule (=> (and (ProjCtx G s f)
               (CtxEq G D)
               (TyEq s t)
               (CtxMorphEq f g))
          (ProjCtx D t g))
      ProjCtx-Congr)

; ProjTm
(rule (=> (and (ProjTm G s M)
               (CtxEq G D)
               (TyEq s t)
               (TmEq M N))
          (ProjTm D t N))
      ProjTm-Congr)

; Extension
(rule (=> (and (Extension f M g)
               (CtxMorphEq f h)
               (TmEq M N)
               (CtxMorphEq g i))
          (Extension h N i))
      Extension-Congr)

; Id
(rule (=> (and (Id M N s)
               (TmEq M O)
               (TmEq N P)
               (TyEq s t))
          (Id O P t))
      Id-Congr)

; Refl
(rule (=> (and (Refl M)
               (TmEq M N))
          (Refl N))
      Refl-Congr)

; Bool
(rule (=> (and (Bool s)
               (TyEq s t))
          (Bool t))
      Bool-Congr)

; True
(rule (=> (and (True M)
               (TmEq M N))
          (True N))
      True-Congr)

; False
(rule (=> (and (False M)
               (TmEq M N))
          (False N))
      False-Congr)

; BoolElim
(rule (=> (and (BoolElim M N O)
               (TmEq M P)
               (TmEq N Q)
               (TmEq O R))
          (BoolElim P Q R))
      BoolElim-Congr)

; Nat
(rule (=> (and (Nat s)
               (TyEq s t))
          (Nat t))
      Nat-Congr)

; Zero
(rule (=> (and (Zero M)
               (TmEq M N))
          (Zero N))
      Zero-Congr)

; Succ
(rule (=> (and (Succ M)
               (TmEq M N))
          (Succ N))
      Succ-Congr)

; NatElim
(rule (=> (and (NatElim M N O)
               (TmEq M P)
               (TmEq N Q)
               (TmEq O R))
          (NatElim P Q R))
      NatElim-Congr)

;;;;;;;;;; Functionality rules ;;;;;;;;;;

(rule (=> (and (IdMorph f) (CtxMorph G f G)
               (IdMorph g) (CtxMorph G g G))
          (CtxMorphEq f g))
      IdMorph-Functional)

(rule (=> (and (TySubst s f t)
               (TySubst s f u))
          (TyEq t u))
      TySubst-Functional)

(rule (=> (and (TmSubst M f N)
               (TmSubst M f O))
          (TmEq N O))
      TmSubst-Functional)

(rule (=> (and (CtxEmpty G) (CtxEmpty D))
          (CtxEq G D))
      CtxEmpty-Functional)

(rule (=> (and (Comprehension G s D)
               (Comprehension G s A))
          (CtxEq D A))
      Comprehension-Functional)

(rule (=> (and (ProjCtx G s f)
               (ProjCtx G s g))
          (CtxMorphEq f g))
      ProjCtx-Functional)

(rule (=> (and (ProjTm G s M)
               (ProjTm G s N))
          (TmEq M N))
      ProjTm-Functional)

(rule (=> (and (Extension f M g)
               (Extension f M h))
          (CtxMorphEq g h))
      Extension-Functional)

(rule (=> (and (Id M N s)
               (Id M N t))
          (TyEq s t))
      Id-Functional)

(rule (=> (and (Refl M) (TmTy G M s)
               (Refl N) (TmTy G N s))
          (TmEq M N))
      Refl-Functional)

(rule (=> (and (Bool s) (Ty G s)
               (Bool t) (Ty G t))
          (TyEq s t))
      Bool-Functional)

(rule (=> (and (True M) (TmTy G M s)
               (True N) (TmTy G N s))
          (TmEq M N))
      True-Functional)

(rule (=> (and (False M) (TmTy G M s)
               (False N) (TmTy G N s))
          (TmEq M N))
      False-Functional)

(rule (=> (and (BoolElim M N O)
               (BoolElim M N P))
          (TmEq O P))
      BoolElim-Functional)

(rule (=> (and (Nat s) (Ty G s)
               (Nat t) (Ty G t))
          (TyEq s t))
      Nat-Functional)

(rule (=> (and (Zero M) (TmTy G M s)
               (Zero N) (TmTy G N s))
          (TmEq M N))
      Zero-Functional)

(rule (=> (and (Succ M) (TmTy G M s)
               (Succ N) (TmTy G N s))
          (TmEq M N))
      Succ-Functional)

(rule (=> (and (NatElim M N O)
               (NatElim M N P))
          (TmEq O P))
      NatElim-Functional)

;;;;;;;;;; Categorical rules ;;;;;;;;;;

; g . id = g
(rule (=> (and (CtxMorph G g D)
               (IdMorph f) (CtxMorph G f G))
          (Comp g f g))
      Comp-Id-1)

; id . f = f
(rule (=> (and (CtxMorph G f D)
               (IdMorph g) (CtxMorph D g D))
          (Comp g f f))
      Comp-Id-2)

; h . (g . f) . h = (h . g) . f
(rule (=> (and (Comp g f gf)
               (Comp h gf hgf)
               (Comp h g hg))
          (Comp hg f hgf))
      Comp-Assoc-1)

(rule (=> (and (Comp h g hg)
               (Comp hg f hgf)
               (Comp g f gf))
          (Comp h gf hgf))
      Comp-Assoc-2)

; s{id} = s
(rule (=> (and (Ty G s)
               (IdMorph f) (CtxMorph G f G))
          (TySubst s f s))
      Ty-Id)

; s{g . f} = s{g}{f}
(rule (=> (and (Comp g f h)
               (TySubst s h t)
               (TySubst s g u))
          (TySubst u f t))
      Ty-Comp-1)

(rule (=> (and (TySubst s g t)
               (TySubst t f u)
               (Comp g f h))
          (TySubst s h u))
      Ty-Comp-2)

; M{id} = M
(rule (=> (and (TmTy G M s)
               (IdMorph f) (CtxMorph G f G))
          (TmSubst M f M))
      Tm-Id)

; M{g . f} = M{g}{f}
(rule (=> (and (Comp g f h)
               (TmSubst M h N)
               (TmSubst M g O))
          (TmSubst O f N))
      Tm-Comp-1)

(rule (=> (and (TmSubst M g N)
               (TmSubst N f O)
               (Comp g f h))
          (TmSubst M h O))
      Tm-Comp-2)

; p(s) . 〈f, M〉 = f
(rule (=> (and (ProjCtx G s p) (CtxMorph B p C)
               (Extension f M e) (CtxMorph A e B))
          (Comp p e f))
      Cons-L)

; v{〈f, N〉} = N
(rule (=> (and (ProjTm G s M) (TmTy D M t)
               (Extension f N e) (CtxMorph A e D))
          (TmSubst M e N))
      Cons-R)

; 〈f, M〉 . g = 〈f . g, M{g}〉
(rule (=> (and (Extension f M e)
               (Comp e g h)
               (Comp f g i)
               (TmSubst M g N))
          (Extension i N h))
      Cons-Natural-1)

(rule (=> (and (Comp f g h)
               (TmSubst M g N)
               (Extension h N e)
               (Extension f M i))
          (Comp i g e))
      Cons-Natural-2)

; 〈p(s), v〉 = id
(rule (=> (and (ProjCtx G s p)
               (ProjTm G s M)
               (Extension p M e))
          (IdMorph e))
      Cons-Id-1)

(rule (=> (and (IdMorph f) (CtxMorph D f D)
               (ProjCtx G s p) (CtxMorph D p G)
               (ProjTm G s M))
          (Extension p M f))
      Cons-Id-2)

;;;;;;;;;; Intermediate rules ;;;;;;;;;;

; <id, M> is M bar
(rule (=> (and (Extension f M e)
               (IdMorph f))
          (TmBar M e))
      TmBar-Fill)

; <f . p1(D.s{f}), p2(D.s{f})> is q(f, s)
(rule (=> (and (CtxMorph G f D)
               (TySubst s f t)
               (ProjCtx D t p)
               (ProjTm D t M)
               (Comp f p g)
               (Extension f M e))
          (Weakening f s e))
      Weakening-Fill)

;;;;;;;;;; Type forming/introduction/elimination ;;;;;;;;;;

; (Id M N){f} = Id M{f} N{f}
(rule (=> (and (Id M N s)
               (TySubst s f t)
               (TmSubst M f Q)
               (TmSubst N f R))
          (Id Q R t))
      Id-Natural-1)

(rule (=> (and (TmSubst M f O)
               (TmSubst N f P)
               (Id O P s)
               (Id M N t))
          (TySubst t f s))
      Id-Natural-2)

; Refl(D){f : G -> D} = Refl(G)
(rule (=> (and (Refl M) (TmTy D M s)
               (CtxMorph G f D)
               (TmSubst M f O))
          (Refl O))
      Refl-Natural-1)

(rule (=> (and (Refl M) (TmTy G M s)
               (Refl N) (TmTy D N t)
               (CtxMorph G f D))
          (TmSubst N f M))
      Refl-Natural-2)

(rule (=> (and (TmTy G M s)
               (Id N O s))
          (TmEq N O))
      Reflection)

(rule (=> (and (TmTy G M s)
               (Id N O s))
          (Refl M))
      Id-Can)

; Bool(D){f : G -> D} = Bool(G)
(rule (=> (and (Bool s) (Ty D s)
               (CtxMorph G f D)
               (TySubst s f t))
          (Bool t))
      Bool-Natural-1)

(rule (=> (and (Bool s) (Ty G s)
               (Bool t) (Ty D t)
               (CtxMorph G f D))
          (TySubst t f s))
      Bool-Natural-2)

; True(D){f : G -> D} = True(G)
(rule (=> (and (True M) (TmTy D M s)
               (CtxMorph G f D)
               (TmSubst M f O))
          (True O))
      True-Natural-1)

(rule (=> (and (True M) (TmTy G M s)
               (True N) (TmTy D N t)
               (CtxMorph G f D))
          (TmSubst N f M))
      True-Natural-2)

; False(D){f : G -> D} = False(G)
(rule (=> (and (False M) (TmTy D M s)
               (CtxMorph G f D)
               (TmSubst M f O))
          (False O))
      False-Natural-1)

(rule (=> (and (False M) (TmTy G M s)
               (False N) (TmTy D N t)
               (CtxMorph G f D))
          (TmSubst N f M))
      False-Natural-2)

; (BoolElim M N){q(f : G -> D, Bool)} = BoolElim M{f} N{f}
(rule (=> (and (BoolElim M N O)
               (CtxMorph G f D)
               (Weakening f s q) (Bool s) (Ty D s)
               (TmSubst O q P)
               (TmSubst M f Q)
               (TmSubst N f R))
          (BoolElim Q R P))
      BoolElim-Natural-1)

(rule (=> (and (BoolElim Q R P)
               (TmSubst M f Q)
               (TmSubst N f R)
               (CtxMorph G f D)
               (BoolElim M N O) 
               (Weakening f s q) (Bool s) (Ty D s))
          (TmSubst O q P))
      BoolElim-Natural-2)

; (BoolElim M N){<id, True>} = M
(rule (=> (and (BoolElim M N O) (TmTy D O s) ; if O is bool-elim
               (TmBar P f) (CtxMorph G f D)  ; and f is P bar
               (True P))                     ; and P is True
          (TmSubst O f M))                   ; then the substitution is the true case.
      BoolElim-True)

; (BoolElim M N){<id, False>} = N
(rule (=> (and (BoolElim M N O) (TmTy D O s) ; if O is bool-elim
               (TmBar P f) (CtxMorph G f D)  ; and f is P bar
               (False P))                    ; and P is False
          (TmSubst O f N))                   ; then the substitution is the false case.
      BoolElim-False)

;; Nat(D){f : G -> D} = Nat(G)
;(rule (=> (and (Nat s) (Ty D s)
;               (CtxMorph G f D)
;               (TySubst s f t))
;          (Nat t))
;      Nat-Natural-1)
;
;(rule (=> (and (Nat s) (Ty D s)
;               (CtxMorph G f D)
;               (Nat t) (Ty G t))
;          (TySubst s f t))
;      Nat-Natural-2)
;
;; Zero(D){f : G -> D} = Zero(G)
;(rule (=> (and (Zero M) (TmTy D M s)
;               (CtxMorph G f D)
;               (TmSubst M f O))
;          (Zero O))
;      Zero-Natural-1)
;
;(rule (=> (and (Zero M) (TmTy G M s)
;               (Zero N) (TmTy D N t)
;               (CtxMorph G f D))
;          (TmSubst N f M))
;      Zero-Natural-2)
;
;; Succ(D){f : G -> D} = Succ(G)
;(rule (=> (and (Succ M) (TmTy D M s)
;               (CtxMorph G f D)
;               (TmSubst M f O))
;          (Succ O))
;      Succ-Natural-1)
;
;(rule (=> (and (Succ O) (TmTy G O t)
;               (Succ M) (TmTy D M s)
;               (CtxMorph G f D))
;          (TmSubst M f O))
;      Succ-Natural-2)
; (NatElim M N){f} = NatElim M{p1 . f . } N
;
;(rule (=> (and (NatElim M N O) (TmTy A O s) (Comprehension G t A)
;               (NatElim P Q R) (TmTy B R u) (Comprehension D v B)
;               (CtxMorph G D f)
;               (TmSubst f P)
; 
;(rule (=> (and (NatElim M N O)   ; if O is nat-elim
;               (TmSubst O f P)   ; and O{f} = P
;               (Extension g Q f) ; and <g, Q> = f
;               (Zero Q))         ; and Q = 0
;          (TmEq P M))            ; then the substitution is the zero case.
;      NatElim-0)
;
;(rule (=> (and (NatElim M N O)    ; if O is nat-elim
;               (TmSubst O f P)    ; and O{f} = P
;               (Extension g Q f)  ; and <g, Q> = f (Q is discriminee)
;               (TmSubst R h Q)    ; and R{h} = Q
;               (Succ R)           ; and R is a successor term
;               (Extension i S h)  ; and <i, S> = h (discriminee is successor of S)
;               (TmSubst N j T)    ; and N{j} = T (successor case is substitution)
;               (Extension k O j)  ; and <k, O> = j (substituting IH by nat-elim itself)
;               (Extension l S k)) ; and <l, S> = k (substituting pred by S)
;          (TmEq P T))
;      NatElim-S)

".Replace("{SortSize}", SortSize.ToString());
    }
}
