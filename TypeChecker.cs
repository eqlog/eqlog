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

        private readonly FuncDecl _nat;
        private readonly FuncDecl _zero;
        private readonly FuncDecl _succ;

        private readonly Z3Expr _G;
        private readonly Z3Expr _f;
        private readonly Z3Expr _s;
        private readonly Z3Expr _M;

        private readonly Dictionary<string, FuncDecl> _rels;
        private readonly Dictionary<uint, string> _dbgInf = new Dictionary<uint, string>();

        private uint _counter;
        private uint NextId() => checked(++_counter);

        private readonly ContextInfo _ctxInfo;

        public TypeChecker()
        {
            _z3Ctx = new Context();
            _fix = _z3Ctx.MkFixedpoint();
            _fix.Parameters =
                _z3Ctx.MkParams()
                //.Add("engine", "spacer")
                //.Add("datalog.generate_explanations", false)
                //.Add("datalog.all_or_nothing_deltas", true)
                //.Add("datalog.unbound_compressor", false)
                ;
            _fix.ParseString(s_z3Setup);

            _sort = _z3Ctx.MkBitVecSort(SortSize);
            _G = _z3Ctx.MkConst("G", _sort);
            _f = _z3Ctx.MkConst("f", _sort);
            _s = _z3Ctx.MkConst("s", _sort);
            _M = _z3Ctx.MkConst("M", _sort);

            _rels = CollectRelations(_fix.Rules);
            _ctxEq = _rels["CtxEq"];
            _ctxMorphEq = _rels["CtxMorphEq"];
            _tyEq = _rels["TyEq"];
            _tmEq = _rels["TmEq"];
            _ctx = _rels["Ctx"];
            _ctxMorph = _rels["CtxMorph"];
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
            _nat = _rels["Nat"];
            _zero = _rels["Zero"];
            _succ = _rels["Succ"];

            uint emptyCtx = NewCtx("");
            _fix.AddFact(_ctxEmpty, emptyCtx);
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

        private uint NewCtx(string? dbg)
        {
            uint id = NextId();
            _fix.AddFact(_ctx, id);
            if (dbg != null)
                _dbgInf.Add(id, dbg);
            return id;
        }

        private uint NewCtxMorph(uint from, uint to, string? dbg)
        {
            uint id = NextId();
            _fix.AddFact(_ctxMorph, from, id, to);
            if (dbg != null)
                _dbgInf.Add(id, dbg);
            return id;
        }

        private uint NewTy(uint ctx, string? dbg)
        {
            uint id = NextId();
            _fix.AddFact(_ty, ctx, id);
            if (dbg != null)
                _dbgInf.Add(id, dbg);
            return id;
        }

        private uint NewTm(uint ctx, uint ty, string? dbg)
        {
            uint id = NextId();
            _fix.AddFact(_tmTy, ctx, id, ty);
            if (dbg != null)
                _dbgInf.Add(id, dbg);
            return id;
        }

        private bool IsTy(uint ctx, uint ty)
        {
            return _fix.Query((BoolExpr)_ty.Apply(BV(ctx), BV(ty))) == Status.SATISFIABLE;
        }

        private bool IsTm(uint ctx, uint tm, uint ty)
        {
            return _fix.Query((BoolExpr)_tmTy.Apply(BV(ctx), BV(tm), BV(ty))) == Status.SATISFIABLE;
        }

        private bool IsComprehension(uint prevCtx, uint ty, uint ctx)
        {
            return _fix.Query((BoolExpr)_comprehension.Apply(BV(prevCtx), BV(ty), BV(ctx))) == Status.SATISFIABLE;
        }

        private BitVecNum BV(uint id) => _z3Ctx.MkBV(id, SortSize);

        private bool IsTmTy(uint ctx, uint tm, uint ty)
        {
            return _fix.Query((BoolExpr)_tmTy.Apply(BV(ctx), BV(tm), BV(ty))) == Status.SATISFIABLE;
        }

        public uint TypeCheck(Def def)
        {
            using (_ctxInfo.Remember())
            {
                foreach (CtxExt ctxExt in def.CtxExts)
                    ExtendContext(ctxExt);

                uint retTyId = TypeCheckType(def.RetTy);
                uint bodyId = TypeCheckTerm(def.Body, retTyId);

                return bodyId;
            }
        }

        private void ExtendContext(CtxExt ext)
        {
            uint id = TypeCheckType(ext.Type);
            _ctxInfo.Add(ext.Name.IsDiscard ? null : ext.Name.Name, id);
        }

        private uint TypeCheckType(Expr expr)
        {
            uint id = TypeCheck(expr);
            if (!IsTy(_ctxInfo.Id, id))
                throw new Exception($"{expr} is not a type");

            return id;
        }

        private uint TypeCheckTerm(Expr expr, uint tyId)
        {
            uint id = TypeCheck(expr);

            if (!IsTmTy(_ctxInfo.Id, id, tyId))
                throw new Exception($"{expr} is not of expected type{(_dbgInf.TryGetValue(tyId, out string? dbg) ? " " + dbg : "")}");

            return id;
        }

        private uint TypeCheck(Expr expr)
        {
            switch (expr)
            {
                case IdExpr { Id: string id }:
                    if (id == "nat")
                        return FormNat();
                    if (id == "O")
                        return IntroduceZero();

                    return _ctxInfo.AccessVar(id);
                case AppExpr { Fun: string fun, Args: var args }:
                    if (fun == "S")
                    {
                        (uint succCtx, uint succTm, uint succNatTy) = IntroduceSucc();
                        uint natTy = FormNat();
                        uint arg = TypeCheckTerm(args.Single(), natTy);

                        // Now we return succTm{<id, arg>}
                        uint idMorph = IdMorph(_ctxInfo.Id);
                        uint ext = Extension(_ctxInfo.Id, succCtx, idMorph, arg);
                        uint tmSubst = SubstTerm(ext, _ctxInfo.Id, natTy, succTm);
                        return tmSubst;
                    }
                    if (fun == "dump")
                    {
                        uint result = TypeCheck(args[1]);
                        string relStr = ((IdExpr)args[0]).Id;
                        string[] rels = relStr == "all" ? _rels.Keys.ToArray() : new[] { relStr };
                        foreach (string rel in rels)
                        {
                            _fix.Query(_rels[rel]);
                            string ans = _fix.GetAnswer().ToString();
                            ans = _dbgInf.Aggregate(
                                    ans,
                                    (acc, kvp) => acc = acc.Replace($"#x{kvp.Key:x8}", "'" + kvp.Value + "'"));
                            Console.WriteLine("------- {0} -------", rel);
                            Console.WriteLine(ans);
                        }
                        return result;
                    }

                    goto default;
                default:
                    throw new Exception("Unhandled: " + expr);
            }
        }

        private uint FormNat()
        {
            if (_fix.Query(_z3Ctx.MkExists(new[] { _s }, _nat.Apply(BV(_ctxInfo.Id), _s))) == Status.SATISFIABLE)
                return ExtractAnswer(0);

            uint natId = NewTy(_ctxInfo.Id, "nat");
            _fix.AddFact(_nat, _ctxInfo.Id, natId);
            return natId;
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

        private uint IntroduceZero()
        {
            if (_fix.Query(_z3Ctx.MkExists(new[] { _M }, _zero.Apply(BV(_ctxInfo.Id), _M))) == Status.SATISFIABLE)
                return ExtractAnswer(0);

            uint zeroId = NewTm(_ctxInfo.Id, FormNat(), "0");
            _fix.AddFact(_zero, _ctxInfo.Id, zeroId);
            return zeroId;
        }

        private (uint ctx, uint tm, uint natTy) IntroduceSucc()
        {
            uint natTy = FormNat();
            Quantifier query =
                _z3Ctx.MkExists(
                    new[] { _G, _M },
                    (BoolExpr)_comprehension.Apply(BV(_ctxInfo.Id), BV(natTy), _G) &
                    (BoolExpr)_succ.Apply(_G, _M));

            if (_fix.Query(query) == Status.SATISFIABLE)
                return (ExtractAnswer(0), ExtractAnswer(1), natTy);

            using (_ctxInfo.Remember())
            {
                _ctxInfo.Add("pred", natTy);
                natTy = FormNat();
                uint succ = NewTm(_ctxInfo.Id, natTy, "succ pred");
                _fix.AddFact(_succ, _ctxInfo.Id, succ);
                return (_ctxInfo.Id, succ, natTy);
            }
        }

        private uint IdMorph(uint ctx)
        {
            if (_fix.Query(_z3Ctx.MkExists(new[] { _f }, _idMorph.Apply(BV(ctx), _f))) == Status.SATISFIABLE)
                return ExtractAnswer(0);

            _dbgInf.TryGetValue(ctx, out string? ctxDbg);
            string? dbg = ctxDbg != null ? $"id({ctxDbg})" : null;

            uint id = NewCtxMorph(ctx, ctx, dbg);
            _fix.AddFact(_idMorph, ctx, id);
            return id;
        }

        private uint Extension(uint ctxFrom, uint ctxTo, uint ctxMorph, uint tm)
        {
            if (_fix.Query(_z3Ctx.MkExists(new[] { _f }, _extension.Apply(BV(ctxMorph), BV(tm), _f))) == Status.SATISFIABLE)
                return ExtractAnswer(0);

            _dbgInf.TryGetValue(ctxMorph, out string? ctxMorphDbg);
            _dbgInf.TryGetValue(tm, out string? tmDbg);
            string? dbg = ctxMorphDbg != null && tmDbg != null ? $"<{ctxMorphDbg}, {tmDbg}>" : null;

            uint id = NewCtxMorph(ctxFrom, ctxTo, dbg);
            _fix.AddFact(_extension, ctxMorph, tm, id);
            return id;
        }

        private uint SubstType(uint ctxMorph, uint newCtx, uint oldTy)
        {
            if (_fix.Query(_z3Ctx.MkExists(new[] { _s }, _tySubst.Apply(BV(oldTy), BV(ctxMorph), _s))) == Status.SATISFIABLE)
                return ExtractAnswer(0);

            _dbgInf.TryGetValue(ctxMorph, out string? ctxMorphDbg);
            _dbgInf.TryGetValue(oldTy, out string? tyDbg);
            string? dbg = ctxMorphDbg != null && tyDbg != null ? $"{tyDbg}{{{ctxMorphDbg}}}" : null;

            uint id = NewTy(newCtx, dbg);
            _fix.AddFact(_tySubst, oldTy, ctxMorph, id);
            return id;
        }

        private uint SubstTerm(uint ctxMorph, uint newCtx, uint newTy, uint oldTm)
        {
            if (_fix.Query(_z3Ctx.MkExists(new[] { _M }, _tmSubst.Apply(BV(oldTm), BV(ctxMorph), _M))) == Status.SATISFIABLE)
                return ExtractAnswer(0);

            _dbgInf.TryGetValue(ctxMorph, out string? ctxMorphDbg);
            _dbgInf.TryGetValue(oldTm, out string? tmDbg);
            string? dbg = ctxMorphDbg != null && tmDbg != null ? $"{tmDbg}{{{ctxMorphDbg}}}" : null;

            uint id = NewTm(newCtx, newTy, dbg);
            _fix.AddFact(_tmSubst, oldTm, ctxMorph, id);
            return id;
        }

        public void Dispose()
        {
            _z3Ctx.Dispose();
        }

        private class ContextInfo
        {
            private readonly TypeChecker _tc;
            private Context Z3 => _tc._z3Ctx;
            private Fixedpoint Fix => _tc._fix;
            private Z3Expr G => _tc._G;
            private BitVecExpr BV(uint id) => _tc.BV(id);

            private readonly List<(uint prevCtx, string? name, uint ty)> _vars =
                new List<(uint prevCtx, string? name, uint ty)>();

            public ContextInfo(TypeChecker tc, uint initialId)
            {
                _tc = tc;
                Id = initialId;
            }

            public int NumVars => _vars.Count;

            public uint Id { get; private set; }

            public void Add(string? name, uint tyId)
            {
                Debug.Assert(_tc.IsTy(Id, tyId), "Type is not a type in this context");

                uint ctx;
                if (Fix.Query(Z3.MkExists(new[] { G }, _tc._comprehension.Apply(BV(Id), BV(tyId), G))) == Status.SATISFIABLE)
                {
                    ctx = _tc.ExtractAnswer(0);
                }
                else
                {
                    string? dbg = ContextDbgString(Id, name, tyId);
                    ctx = _tc.NewCtx(dbg);
                    Fix.AddFact(_tc._comprehension, Id, tyId, ctx);
                }

                _vars.Add((Id, name, tyId));
                Id = ctx;
            }

            private string? ContextDbgString(uint ctx, string? name, uint tyId)
            {
                return
                    _tc._dbgInf.TryGetValue(ctx, out string? prevCtxDbg) &&
                    _tc._dbgInf.TryGetValue(tyId, out string? tyDbg)
                    ? string.Format("{0}{1} : {2}", prevCtxDbg == "" ? "" : $"{prevCtxDbg}, ", name ?? "_", tyDbg)
                    : null;
            }

            // Construct a term that accesses the var by the specified name.
            public uint AccessVar(string name)
            {
                int index = _vars.FindIndex(t => t.name == name);
                if (index == -1)
                    throw new ArgumentException($"No variable exists by name {name}", nameof(name));

                // Go(G, x : s |- x : s) = p2(s)
                // Go(G, x : s, D, y : t |- x : s) = Go(G, x : s, D |- x : s){p(t)}

                (uint tmId, uint tyId) Go(int i, uint nextCtx)
                {
                    (uint ctx, string? name, uint addedTy) = _vars[i];
                    _tc._dbgInf.TryGetValue(addedTy, out string? tyDbg);
                    string? ctxMorphDbg = tyDbg != null ? $"p1({tyDbg})" : null;

                    // Make context morphism that gets us from nextCtx to ctx by projecting out added variable.
                    uint ctxProj = _tc.NewCtxMorph(nextCtx, ctx, ctxMorphDbg);
                    Fix.AddFact(_tc._projCtx, ctx, addedTy, ctxProj);

                    if (i == index)
                    {
                        // addedTy is in ctx, and we want it in nextCtx, so
                        // make addedTy{ctxProj} = tySubst in nextCtx.
                        uint tySubst = _tc.SubstType(ctxProj, nextCtx, addedTy);

                        uint tmProj = _tc.NewTm(nextCtx, tySubst, name);
                        Fix.AddFact(_tc._projTm, ctx, addedTy, tmProj);
                        return (tmProj, tySubst);
                    }
                    else
                    {
                        (uint tm, uint ty) = Go(i - 1, ctx);
                        // nextCtx = ctx, x : ty[in ctx]
                        // tm is term that accesses variable in ctx
                        // ty is type of variable in ctx

                        Debug.Assert(_tc.IsComprehension(ctx, addedTy, nextCtx));
                        Debug.Assert(_tc.IsTy(ctx, ty));
                        Debug.Assert(_tc.IsTm(ctx, tm, ty));

                        uint tySubst = _tc.SubstType(ctxProj, nextCtx, ty);
                        uint tmSubst = _tc.SubstTerm(ctxProj, nextCtx, tySubst, tm);
                        return (tmSubst, tySubst);
                    }
                }

                return Go(_vars.Count - 1, Id).tmId;
            }

            public ContextSavePoint Remember()
                => new ContextSavePoint(this);

            public struct ContextSavePoint : IDisposable
            {
                private readonly ContextInfo _ctx;
                private readonly int _numVars;
                private readonly uint _id;
                public ContextSavePoint(ContextInfo ctx)
                {
                    _ctx = ctx;
                    _numVars = ctx._vars.Count;
                    _id = ctx.Id;
                }

                public void Dispose()
                {
                    Debug.Assert(_ctx._vars.Count >= _numVars);

                    _ctx._vars.RemoveRange(_numVars, _ctx._vars.Count - _numVars);
                    _ctx.Id = _id;
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
; Comp g f h -- h is g . f
(declare-rel Comp (CtxMorphS CtxMorphS CtxMorphS))
; Ty G s -- G |- s type
(declare-rel Ty (CtxS TyS))
; TmTy G M s -- G |- M : s
(declare-rel TmTy (CtxS TmS TyS))

; Functional relations
; IdMorph G f -- f is the identity context morphism for G
(declare-rel IdMorph (CtxS CtxMorphS))
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

; Type forming/introduction/elimination
(declare-rel Nat (CtxS TyS))
(declare-rel Zero (CtxS TmS))
; Succ G M -- M is successor term in G (which is of the form D, pred : nat).
(declare-rel Succ (CtxS TmS))

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

(declare-var r TyS)
(declare-var s TyS)
(declare-var t TyS)
(declare-var u TyS)
(declare-var v TyS)

(declare-var M TmS)
(declare-var N TmS)
(declare-var O TmS)
(declare-var P TmS)
(declare-var Q TmS)

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
               (CtxEq G D))
          (Ty D s))
      Ty-Ctxv)

; TmTy
(rule (=> (and (TmTy G M s)
               (CtxEq G D)
               (TyEq s t))
          (TmTy D M t))
      Tm-Ctxv)

; IdMorph
(rule (=> (and (IdMorph G f)
               (CtxEq G D)
               (CtxMorphEq f g))
          (IdMorph D g))
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

; Nat
(rule (=> (and (Nat G s)
               (CtxEq G D)
               (TyEq s t))
          (Nat D t))
      Nat-Congr)

; Zero
(rule (=> (and (Zero G M)
               (CtxEq G D)
               (TmEq M N))
          (Zero D N))
      Zero-Congr)

; Succ
(rule (=> (and (Succ G M)
               (CtxEq G D)
               (TmEq M N))
          (Succ D N))
      Succ-Congr)

;;;;;;;;;; Functionality rules ;;;;;;;;;;

(rule (=> (and (IdMorph G f)
               (IdMorph G g))
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

(rule (=> (and (Nat G s)
               (Nat G t))
          (TyEq s t))
      Nat-Functional)

(rule (=> (and (Zero G M)
               (Zero G N))
          (TmEq M N))
      Zero-Functional)

(rule (=> (and (Succ G M)
               (Succ G N))
          (TmEq M N))
      Succ-Functional)

;;;;;;;;;; Categorical rules ;;;;;;;;;;

; (f . g) . h = f . (h . g)
(rule (=> (and (Comp f g i)
               (Comp i h j)
               (Comp h g k)
               (Comp f k l))
          (CtxMorphEq j l))
      Comp-Assoc)

; s{id} = s
(rule (=> (and (TySubst s f t)
               (IdMorph G f))
          (TyEq s t))
      Ty-Id)

; s{g . f} = s{g}{f}
(rule (=> (and (Comp g f h)
               (TySubst s h t)
               (TySubst s g u)
               (TySubst u f v))
          (TyEq t v))
      Ty-Comp)

; M{id} = M
(rule (=> (and (TmSubst M f N)
               (IdMorph G f))
          (TmEq M N))
      Tm-Id)

; M{g . f} = M{g}{f}
(rule (=> (and (Comp g f h)
               (TmSubst M h N)
               (TmSubst M g O)
               (TmSubst O f P))
          (TmEq N P))
      Tm-Comp)

; p(s) . 〈f, M〉= f
(rule (=> (and (ProjCtx G s p)
               (Extension f M e)
               (Comp p e g))
          (CtxMorphEq g f))
      Cons-L)

; M = v /\ 〈f, N〉= e /\ M{e} = O => O = N
(rule (=> (and (ProjTm G s M)
               (Extension f N e)
               (TmSubst M e O))
          (TmEq O N))
      Cons-R)

; 〈f, M〉. g = 〈f . g, M{g}〉
; 〈f, M〉 = e /\ e . g = h /\ f . g = i /\ M{g} = N /\ 〈i, N〉= j
; => h = j
(rule (=> (and (Extension f M e)
               (Comp e g h)
               (Comp f g i)
               (TmSubst M g N)
               (Extension i N j))
          (CtxMorphEq h j))
      Cons-Natural)

; 〈p(s), v〉= id
; p(s) = p /\ M = v /\ 〈p, M〉= e /\ id = f => e = f
(rule (=> (and (ProjCtx G s p)
               (ProjTm G s M)
               (Extension p M e)
               (Comprehension G s D)
               (IdMorph D f))
          (CtxMorphEq e f))
      Cons-Id)

;;;;;;;;;; Type forming/introduction/elimination ;;;;;;;;;;

; Nat^D{f : G -> D} = Nat^G
(rule (=> (and (Nat G s)
               (Nat D t)
               (CtxMorph G f D)
               (TySubst t f u))
          (TyEq u s))
      Nat-Natural)

; Zero^D{f : G -> D} = Zero^G
(rule (=> (and (Zero G M)
               (Zero D N)
               (CtxMorph G f D)
               (TmSubst N f O))
          (TmEq O M))
      Zero-Natural)

; Succ^D{f : G -> D} = Succ^G
(rule (=> (and (Succ G M)
               (Succ D N)
               (CtxMorph G f D)
               (TmSubst N f O))
          (TmEq O M))
      Succ-Natural)

".Replace("{SortSize}", SortSize.ToString());
    }
}
