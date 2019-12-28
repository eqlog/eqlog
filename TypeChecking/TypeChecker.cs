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

        private readonly FuncDecl _nat;
        private readonly FuncDecl _zero;
        private readonly FuncDecl _succ;
        private readonly FuncDecl _natElim;

        private readonly Z3Expr _G;
        private readonly Z3Expr _f;
        private readonly Z3Expr _s;
        private readonly Z3Expr _M;

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
            _nat = _rels["Nat"];
            _zero = _rels["Zero"];
            _succ = _rels["Succ"];
            _natElim = _rels["NatElim"];

            ModelCtx emptyCtx = NewCtx("");
            _fix.AddFact(_ctxEmpty, emptyCtx.Id);
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

        private ModelCtx NewCtx(string? dbg)
        {
            uint id = NextId();
            _fix.AddFact(_ctx, id);
            var ctx = new ModelCtx(id);
            if (dbg != null)
                _debugInfo.Add(id, dbg);
            return WithDbg(ctx);
        }

        private CtxMorphism NewCtxMorph(ModelCtx from, ModelCtx to, string? dbg)
        {
            uint id = NextId();
            _fix.AddFact(_ctxMorph, from.Id, id, to.Id);
            var ctxMorph = new CtxMorphism(id, from, to);
            if (dbg != null)
                _debugInfo.Add(id, dbg);
            return WithDbg(ctxMorph);
        }

        private Ty NewTy(ModelCtx ctx, string? dbg)
        {
            uint id = NextId();
            _fix.AddFact(_ty, ctx.Id, id);
            var ty = new Ty(id, ctx);
            if (dbg != null)
                _debugInfo.Add(id, dbg);
            return WithDbg(ty);
        }

        private Tm NewTm(Ty ty, string? dbg)
        {
            uint id = NextId();
            _fix.AddFact(_tmTy, ty.Context.Id, id, ty.Id);
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
            _ctxInfo.Add(ext.Name.IsDiscard ? null : ext.Name.Name, ty);
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
                throw new Exception($"{expr} is not of expected type {ty.GetDebugInfo() ?? ""}");

            return tm;
        }

        private ModelObject TypeCheck(Expr expr)
        {
            switch (expr)
            {
                case IdExpr { Id: string id }:
                    if (id == "nat")
                        return FormNat(_ctxInfo.Ctx);
                    if (id == "O")
                        return IntroduceZero(FormNat(_ctxInfo.Ctx));

                    return _ctxInfo.AccessVar(id);
                case AppExpr { Fun: string fun, Args: var args }:
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
                        string relStr = ((IdExpr)args[0]).Id;
                        string[] rels = relStr == "all" ? _rels.Keys.ToArray() : new[] { relStr };
                        foreach (string rel in rels)
                        {
                            _fix.Query(_rels[rel]);
                            string ans = _fix.GetAnswer().ToString();
                            ans = ModelObject.DbgInfo.Aggregate(
                                    ans,
                                    (acc, kvp) => acc.Replace($"#x{kvp.Key.Id:x8}", "'" + kvp.Value + "'"));
                            Console.WriteLine("------- {0} -------", rel);
                            Console.WriteLine(ans);
                        }
                        return result;
                    }

                    goto default;
                case ElimExpr elim:
                    Tm discTm = TypeCheckAnyTerm(elim.Discriminee);
                    if (IsTyEq(discTm.Ty, FormNat(_ctxInfo.Ctx)))
                        return ElimNat(discTm, elim);

                    goto default;
                default:
                    throw new Exception("Unhandled: " + expr);
            }
        }

        private ModelCtx Comprehension(ModelCtx ctx, Ty ty, string? nameForDbg)
        {
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
            _fix.AddFact(_comprehension, ctx.Id, ty.Id, newCtx.Id);
            return newCtx;
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
            _fix.AddFact(_nat, nat.Id);
            return nat;
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
            _fix.AddFact(_zero, zero.Id);
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
            _fix.AddFact(_succ, succ.Id);
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
            Tm projTm = ProjTm(substTy, substTyInCtxFrom, null);

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
            _fix.AddFact(_projCtx, removedTy.Context.Id, removedTy.Id, ctxMorphism.Id);
            return ctxMorphism;
        }

        private Tm ProjTm(Ty addedVarTy, Ty fullTy, string? dbgName)
        {
            if (_fix.Query(_z3Ctx.MkExists(new[] { _M }, _projTm.Apply(BV(addedVarTy.Context), BV(addedVarTy), _M))) == Status.SATISFIABLE)
                return WithDbg(new Tm(ExtractAnswer(0), fullTy));

            string? dbg = dbgName;
            if (dbg == null)
            {
                string? tyDbg = addedVarTy.GetDebugInfo();
                dbg = tyDbg != null ? $"p2({tyDbg})" : null;
            }

            Tm tm = NewTm(fullTy, dbg);
            _fix.AddFact(_projTm, addedVarTy.Context.Id, addedVarTy.Id, tm.Id);
            return tm;
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
            _fix.AddFact(_natElim, zeroCase.Id, succCase.Id, elimTm.Id);

            CtxMorphism addDisc = TermBar(discriminee, intoTy.Context);
            Tm substTm = SubstTermAndType(elimTm, addDisc);
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
            _fix.AddFact(_idMorph, ctxMorphism.Id);
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
            _fix.AddFact(_comp, g.Id, f.Id, gf.Id);
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
            _fix.AddFact(_extension, morphism.Id, tm.Id, newMorphism.Id);
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
            _fix.AddFact(_tySubst, oldTy.Id, morphism.Id, newTy.Id);
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
            _fix.AddFact(_tmSubst, oldTm.Id, morphism.Id, tm.Id);
            return tm;
        }

        private Tm SubstTermAndType(Tm oldTm, CtxMorphism morphism)
        {
            Ty newTy = SubstType(oldTm.Ty, morphism);
            return SubstTerm(oldTm, morphism, newTy);
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
            private BitVecExpr BV(ModelObject obj) => _tc.BV(obj);

            private readonly List<(string? name, Ty ty)> _vars = new List<(string? name, Ty ty)>();

            public ContextInfo(TypeChecker tc, ModelCtx initialCtx)
            {
                _tc = tc;
                Ctx = initialCtx;
            }

            public int NumVars => _vars.Count;

            public ModelCtx Ctx { get; private set; }

            public void Add(string? name, Ty ty)
            {
                Debug.Assert(_tc.IsCtxEq(ty.Context, Ctx));

                ModelCtx newCtx = _tc.Comprehension(Ctx, ty, name);
                _vars.Add((name, ty));
                Ctx = newCtx;
            }

            // Construct a term that accesses the var by the specified name.
            public Tm AccessVar(string name)
            {
                int index = _vars.FindIndex(t => t.name == name);
                if (index == -1)
                    throw new ArgumentException($"No variable exists by name {name}", nameof(name));

                Tm Go(int i, ModelCtx nextCtx)
                {
                    (string? name, Ty ty) = _vars[i];
                    // Make context morphism that gets us from nextCtx to ty's ctx by projecting out added variable.
                    CtxMorphism ctxProj = _tc.ProjCtx(nextCtx, ty);

                    if (i == index)
                    {
                        // addedTy is in ctx, and we want it in nextCtx, so
                        // make addedTy{ctxProj} = tySubst in nextCtx.
                        Ty tySubst = _tc.SubstType(ty, ctxProj);

                        Tm tmProj = _tc.ProjTm(ty, tySubst, name);
                        return tmProj;
                    }
                    else
                    {
                        Tm tm = Go(i - 1, ty.Context);
                        // nextCtx = ctx, x : ty[in ctx]
                        // tm is term that accesses variable in ty's ctx
                        // ty is type of variable in ctx

                        Debug.Assert(_tc.IsComprehension(ty, nextCtx));
                        Debug.Assert(_tc.IsCtxEq(tm.Context, ty.Context));

                        Tm tmSubst = _tc.SubstTermAndType(tm, ctxProj);
                        return tmSubst;
                    }
                }

                return Go(_vars.Count - 1, Ctx);
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
; Comp g f h -- h is g . f
(declare-rel Comp (CtxMorphS CtxMorphS CtxMorphS))
; Ty G s -- G |- s type
(declare-rel Ty (CtxS TyS))
; TmTy G M s -- G |- M : s
(declare-rel TmTy (CtxS TmS TyS))

; Functional relations
; IdMorph f -- f is an identity context morphism
(declare-rel IdMorph (CtxMorphS))
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

;; (f . g) . h = f . (g . h)
;(rule (=> (and (Comp f g i)
;               (Comp i h j)
;               (Comp g h k)
;               (Comp f k l))
;          (CtxMorphEq j l))
;      Comp-Assoc)
;; s{id} = s
;(rule (=> (and (TySubst s f t)
;               (IdMorph f))
;          (TyEq s t))
;      Ty-Id)
;; s{g . f} = s{g}{f}
;(rule (=> (and (Comp g f h)
;               (TySubst s h t)
;               (TySubst s g u)
;               (TySubst u f v))
;          (TyEq t v))
;      Ty-Comp)
;; M{id} = M
;(rule (=> (and (TmSubst M f N)
;               (IdMorph f))
;          (TmEq M N))
;      Tm-Id)
;; M{g . f} = M{g}{f}
;(rule (=> (and (Comp g f h)
;               (TmSubst M h N)
;               (TmSubst M g O)
;               (TmSubst O f P))
;          (TmEq N P))
;      Tm-Comp)
;; p(s) . 〈f, M〉= f
;(rule (=> (and (ProjCtx G s p)
;               (Extension f M e)
;               (Comp p e g))
;          (CtxMorphEq g f))
;      Cons-L)
;; M = v /\ 〈f, N〉= e /\ M{e} = O => O = N
;(rule (=> (and (ProjTm G s M)
;               (Extension f N e)
;               (TmSubst M e O))
;          (TmEq O N))
;      Cons-R)
;
;; 〈f, M〉. g = 〈f . g, M{g}〉
;; 〈f, M〉 = e /\ e . g = h /\ f . g = i /\ M{g} = N /\ 〈i, N〉= j
;; => h = j
;(rule (=> (and (Extension f M e)
;               (Comp e g h)
;               (Comp f g i)
;               (TmSubst M g N)
;               (Extension i N j))
;          (CtxMorphEq h j))
;      Cons-Natural)

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
(rule (=> (and (TySubst s f t)
               (IdMorph f))
          (TyEq s t))
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
(rule (=> (and (TmSubst M f N)
               (IdMorph f))
          (TmEq M N))
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
(rule (=> (and (ProjCtx G s p)
               (Extension f M e))
          (Comp p e f))
      Cons-L)

; v{〈f, N〉} = N
; M = v /\ 〈f, N〉= e => M{e} = N
(rule (=> (and (ProjTm G s M) (TmTy D M t)
               (Extension f N e) (CtxMorph A e D))
          (TmSubst M e N))
      Cons-R)

; 〈f, M〉 . g = 〈f . g, M{g}〉
(rule (=> (and (Extension f M e)
               (Comp e g h)
               (Comp f g i)
               (TmSubst M g N))
          (Extension i N e))
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
          (IdMorph f))
      Cons-Id-1)

(rule (=> (and (IdMorph f) (CtxMorph D f D)
               (ProjCtx G s p) (CtxMorph D p G)
               (ProjTm G s M))
          (Extension p M f))
      Cons-Id-2)

;;;;;;;;;; Type forming/introduction/elimination ;;;;;;;;;;

; Nat(D){f : G -> D} = Nat(G)
(rule (=> (and (Nat s) (Ty D s)
               (CtxMorph G f D)
               (TySubst s f t))
          (Nat t))
      Nat-Natural)

; Zero(D){f : G -> D} = Zero(G)
(rule (=> (and (Zero M) (TmTy D M s)
               (CtxMorph G f D)
               (TmSubst N f O))
          (Zero O))
      Zero-Natural)

; Succ(D){f : G -> D} = Succ(G)
(rule (=> (and (Succ M) (TmTy D M s)
               (CtxMorph G f D)
               (TmSubst N f O))
          (Succ O))
      Succ-Natural)

; Given
; D, discriminee : nat |- O : s
; D |- M : s[discriminee := 0]
; D, pred : nat, IH : s[discriminee := pred] |- N : s[discriminee := S pred]
; NatElim M N O
;
; G, discriminee : nat |- R : t
; G |- P : t[discriminee := 0]
; G, pred : nat, IH : t[discriminee := pred] |- Q : t[discriminee := S pred]
; NatElim P Q R
;
; Viewing these as functions giving O and R the naturality conditions states that,
; for any f : G -> D, d : nat, we have
; (NatElim M N){f} = NatElim M{p1 . f . } N
;(rule (=> (and (NatElim M N O) (TmTy A O s) (Comprehension G t A)
;               (NatElim P Q R) (TmTy B R u) (Comprehension D v B)
;               (CtxMorph G D f)
;               (TmSubst  f P)
; 
(rule (=> (and (NatElim M N O)   ; if O is nat-elim
               (TmSubst O f P)   ; and O{f} = P
               (Extension g Q f) ; and <g, Q> = f
               (Zero Q))         ; and Q = 0
          (TmEq P M))            ; then the substitution is the zero case.
      NatElim-0)

(rule (=> (and (NatElim M N O)   ; if O is nat-elim
               (TmSubst O f P)   ; and O{f} = P
               (Extension g Q f) ; and <g, Q> = f (Q is discriminee)
               (TmSubst R h Q)   ; and R{h} = Q
               (Succ R)          ; and R is a successor term
               (Extension i S h) ; and <i, S> = h (discriminee is successor of S)
               (TmSubst N j T)   ; and N{j} = T (successor case is substitution)
               (Extension k O j) ; and <k, O> = j (substituting IH by nat-elim itself)
               (Extension l S k)); and <l, S> = k (substituting pred by S)
          (TmEq P T))
      NatElim-S)

".Replace("{SortSize}", SortSize.ToString());
    }
}
