using Microsoft.Z3;
using QT.TypeChecking;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using Z3Expr = Microsoft.Z3.Expr;

namespace QT
{
    internal class Z3Model : IModel, IDisposable
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


        private readonly Z3Expr _A, _B, _C, _D, _E, _F, _G;
        private readonly Z3Expr _f, _g, _gf;
        private readonly Z3Expr _s, _t;
        private readonly Z3Expr _M, _N;

        private readonly Dictionary<string, FuncDecl> _rels;

        private uint _counter;
        private uint NextId() => checked(++_counter);

        public Z3Model()
        {
            _z3Ctx = new Context();
            _fix = _z3Ctx.MkFixedpoint();
            _fix.Parameters =
                _z3Ctx.MkParams()
                .Add("ctrl_c", false)
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
        }

        public void Dispose()
        {
            _z3Ctx.Dispose();
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

        public bool CtxEq(Ctx ctx1, Ctx ctx2)
            => _fix.Query((BoolExpr)_ctxEq.Apply(BV(ctx1), BV(ctx2))) == Status.SATISFIABLE;

        public bool MorphEq(CtxMorph morph1, CtxMorph morph2)
            => _fix.Query((BoolExpr)_ctxMorphEq.Apply(BV(morph1), BV(morph2))) == Status.SATISFIABLE;

        public bool TyEq(Ty ty1, Ty ty2)
            => _fix.Query((BoolExpr)_tyEq.Apply(BV(ty1), BV(ty2))) == Status.SATISFIABLE;

        public bool TmEq(Tm tm1, Tm tm2)
            => _fix.Query((BoolExpr)_tmEq.Apply(BV(tm1), BV(tm2))) == Status.SATISFIABLE;

        private BitVecNum BV(CwfNode node) => _z3Ctx.MkBV(node.Id, SortSize);

        private uint GetOrMakeId(BoolExpr query)
        {
            if (_fix.Query(query) == Status.SATISFIABLE)
                return ExtractAnswer(0);

            return NextId();
        }

        public EmptyCtx EmptyCtx()
        {
            EmptyCtx ctx = new EmptyCtx(NextId());
            AddCtx(ctx);
            AddAndVerify(_ctxEmpty, ctx.Id);
            return ctx;
        }

        private readonly Dictionary<(uint, uint), ComprehensionCtx> _compCache = new Dictionary<(uint, uint), ComprehensionCtx>();
        public ComprehensionCtx Comprehension(Ctx baseCtx, Ty ty)
        {
            if (_compCache.TryGetValue((baseCtx.Id, ty.Id), out var c))
                return c;

            Debug.Assert(CtxEq(baseCtx, ty.Ctx));

            Quantifier query = _z3Ctx.MkExists(new[] { _G }, _comprehension.Apply(BV(baseCtx), BV(ty), _G));

            ComprehensionCtx ctx = new ComprehensionCtx(GetOrMakeId(query), baseCtx, ty);
            AddCtx(ctx);
            AddAndVerify(_comprehension, baseCtx.Id, ty.Id, ctx.Id);
            return _compCache[(baseCtx.Id, ty.Id)] = ctx;
        }

        private readonly Dictionary<uint, ProjMorph> _projCtxCache = new Dictionary<uint, ProjMorph>();
        public ProjMorph ProjCtx(ComprehensionCtx ctx)
        {
            if (_projCtxCache.TryGetValue(ctx.Id, out var m))
                return m;

            Quantifier query =
                _z3Ctx.MkExists(
                    new[] { _f },
                    _projCtx.Apply(BV(ctx.BaseCtx), BV(ctx.CompTy), _f));

            ProjMorph morph = new ProjMorph(GetOrMakeId(query), ctx);
            AddMorph(morph);
            AddAndVerify(_projCtx, ctx.BaseCtx.Id, ctx.CompTy.Id, morph.Id);
            return _projCtxCache[ctx.Id] = morph;
        }

        private readonly Dictionary<uint, ProjTm> _projTmCache = new Dictionary<uint, ProjTm>();
        public ProjTm ProjTm(ComprehensionCtx ctx)
        {
            if (_projTmCache.TryGetValue(ctx.Id, out var t))
                return t;

            Quantifier query =
                _z3Ctx.MkExists(
                    new[] { _M },
                    _projTm.Apply(BV(ctx.BaseCtx), BV(ctx.CompTy), _M));

            ProjMorph projCtx = ProjCtx(ctx);
            Ty ty = SubstType(ctx.CompTy, projCtx);
            ProjTm tm = new ProjTm(GetOrMakeId(query), ty);
            AddTm(tm);
            AddAndVerify(_projTm, ctx.BaseCtx.Id, ctx.CompTy.Id, tm.Id);
            return _projTmCache[ctx.Id] = tm;
        }

        private readonly Dictionary<uint, IdMorph> _idMorphCache = new Dictionary<uint, IdMorph>();
        public IdMorph IdMorph(Ctx ctx)
        {
            if (_idMorphCache.TryGetValue(ctx.Id, out var m))
                return m;

            Quantifier query =
                _z3Ctx.MkExists(
                    new[] { _f, },
                    (BoolExpr)_idMorph.Apply(_f) &
                    (BoolExpr)_ctxMorph.Apply(BV(ctx), _f, BV(ctx)));

            IdMorph morph = new IdMorph(GetOrMakeId(query), ctx);
            AddMorph(morph);
            AddAndVerify(_idMorph, morph.Id);
            return _idMorphCache[ctx.Id] = morph;
        }

        private readonly Dictionary<(uint, uint), CompMorph> _compMorphCache = new Dictionary<(uint, uint), CompMorph>();
        public CompMorph Compose(CtxMorph g, CtxMorph f)
        {
            if (_compMorphCache.TryGetValue((g.Id, f.Id), out var m))
                return m;

            Debug.Assert(CtxEq(f.Codomain, g.Domain));

            Quantifier query =
                _z3Ctx.MkExists(
                    new[] { _gf },
                    _comp.Apply(BV(g), BV(f), _gf));

            CompMorph gf = new CompMorph(GetOrMakeId(query), g, f);
            AddMorph(gf);
            AddAndVerify(_comp, g.Id, f.Id, gf.Id);
            return _compMorphCache[(g.Id, f.Id)] = gf;
        }

        private readonly Dictionary<(uint, uint, uint), ExtensionMorph> _extensionCache = new Dictionary<(uint, uint, uint), ExtensionMorph>();
        public ExtensionMorph Extension(CtxMorph morph, Tm tm, Ty compTy)
        {
            if (_extensionCache.TryGetValue((morph.Id, tm.Id, compTy.Id), out var m))
                return m;

            Debug.Assert(CtxEq(morph.Domain, tm.Ctx));

            Quantifier query =
                _z3Ctx.MkExists(
                    new[] { _f },
                    _extension.Apply(
                        BV(morph),
                        BV(tm),
                        _f));

            ExtensionMorph ext = new ExtensionMorph(GetOrMakeId(query), morph, tm, Comprehension(morph.Codomain, compTy));
            AddMorph(ext);
            AddAndVerify(_extension, morph.Id, tm.Id, ext.Id);
            return _extensionCache[(morph.Id, tm.Id, compTy.Id)] = ext;
        }

        private readonly Dictionary<(uint, uint), SubstTy> _substTypeCache = new Dictionary<(uint, uint), SubstTy>();
        public SubstTy SubstType(Ty baseTy, CtxMorph morph)
        {
            if (_substTypeCache.TryGetValue((baseTy.Id, morph.Id), out var s))
                return s;

            Debug.Assert(CtxEq(baseTy.Ctx, morph.Codomain));

            Quantifier query = _z3Ctx.MkExists(new[] { _s }, _tySubst.Apply(BV(baseTy), BV(morph), _s));

            SubstTy ty = new SubstTy(GetOrMakeId(query), baseTy, morph);
            AddTy(ty);
            AddAndVerify(_tySubst, baseTy.Id, morph.Id, ty.Id);
            return _substTypeCache[(baseTy.Id, morph.Id)] = ty;
        }

        private readonly Dictionary<(uint, uint), SubstTm> _substTermCache = new Dictionary<(uint, uint), SubstTm>();
        public SubstTm SubstTerm(Tm baseTm, CtxMorph morph)
        {
            if (_substTermCache.TryGetValue((baseTm.Id, morph.Id), out var t))
                return t;

            Debug.Assert(CtxEq(baseTm.Ctx, morph.Codomain));

            Quantifier query = _z3Ctx.MkExists(new[] { _M }, _tmSubst.Apply(BV(baseTm), BV(morph), _M));

            SubstTy newTy = SubstType(baseTm.Ty, morph);
            SubstTm tm = new SubstTm(GetOrMakeId(query), baseTm, morph, newTy);
            AddTm(tm);
            AddAndVerify(_tmSubst, baseTm.Id, morph.Id, tm.Id);
            return _substTermCache[(baseTm.Id, morph.Id)] = tm;
        }

        private readonly Dictionary<(uint, uint), IdTy> _idCache = new Dictionary<(uint, uint), IdTy>();
        public IdTy Id(Tm left, Tm right)
        {
            if (_idCache.TryGetValue((left.Id, right.Id), out var s))
                return s;

            Debug.Assert(TyEq(left.Ty, right.Ty)); // Relax this?

            Quantifier query =
                _z3Ctx.MkExists(
                    new[] { _s },
                    (BoolExpr)_id.Apply(BV(left), BV(right), _s));

            IdTy ty = new IdTy(GetOrMakeId(query), left, right);
            AddTy(ty);
            AddAndVerify(_id, left.Id, right.Id, ty.Id);
            return _idCache[(left.Id, right.Id)] = ty;
        }

        private readonly Dictionary<uint, ReflTm> _reflCache = new Dictionary<uint, ReflTm>();
        public ReflTm Refl(Tm tm)
        {
            if (_reflCache.TryGetValue(tm.Id, out var t))
                return t;

            IdTy idTy = Id(tm, tm);

            Quantifier query =
                _z3Ctx.MkExists(
                    new[] { _M },
                    (BoolExpr)_refl.Apply(_M) &
                    (BoolExpr)_tmTy.Apply(BV(tm.Ctx), _M, BV(idTy)));

            ReflTm reflTm = new ReflTm(GetOrMakeId(query), tm, idTy);
            AddTm(reflTm);
            AddAndVerify(_refl, reflTm.Id);
            return _reflCache[tm.Id] = reflTm;
        }

        private readonly Dictionary<uint, BoolTy> _boolCache = new Dictionary<uint, BoolTy>();
        public BoolTy Bool(Ctx ctx)
        {
            if (_boolCache.TryGetValue(ctx.Id, out var s))
                return s;

            Quantifier query =
                _z3Ctx.MkExists(
                    new[] { _s },
                    (BoolExpr)_bool.Apply(_s) &
                    (BoolExpr)_ty.Apply(BV(ctx), _s));

            BoolTy ty = new BoolTy(GetOrMakeId(query), ctx);
            AddTy(ty);
            AddAndVerify(_bool, ty.Id);
            return _boolCache[ctx.Id] = ty;
        }

        private readonly Dictionary<uint, TrueTm> _trueCache = new Dictionary<uint, TrueTm>();
        public TrueTm True(Ctx ctx)
        {
            if (_trueCache.TryGetValue(ctx.Id, out var t))
                return t;

            BoolTy boolTy = Bool(ctx);

            Quantifier query =
                _z3Ctx.MkExists(
                    new[] { _M },
                    (BoolExpr)_true.Apply(_M) &
                    (BoolExpr)_tmTy.Apply(BV(boolTy.Ctx), _M, BV(boolTy)));

            TrueTm tm = new TrueTm(GetOrMakeId(query), boolTy);
            AddTm(tm);
            AddAndVerify(_true, tm.Id);
            return _trueCache[ctx.Id] = tm;
        }

        private readonly Dictionary<uint, FalseTm> _falseCache = new Dictionary<uint, FalseTm>();
        public FalseTm False(Ctx ctx)
        {
            if (_falseCache.TryGetValue(ctx.Id, out var t))
                return t;

            BoolTy boolTy = Bool(ctx);

            Quantifier query =
                 _z3Ctx.MkExists(
                     new[] { _M },
                     (BoolExpr)_false.Apply(_M) &
                     (BoolExpr)_tmTy.Apply(BV(boolTy.Ctx), _M, BV(boolTy)));

            FalseTm tm = new FalseTm(GetOrMakeId(query), boolTy);
            AddTm(tm);
            AddAndVerify(_false, tm.Id);
            return _falseCache[ctx.Id] = tm;
        }

        public ElimBoolTm ElimBool(Ty intoTy, Tm trueCase, Tm falseCase)
        {
            Debug.Assert(intoTy.Ctx is ComprehensionCtx intoCtx &&
                         TyEq(intoCtx.CompTy, Bool(intoCtx.CompTy.Ctx)) &&
                         CtxEq(trueCase.Ctx, intoCtx.BaseCtx) &&
                         CtxEq(falseCase.Ctx, intoCtx.BaseCtx));

            ElimBoolTm tm = new ElimBoolTm(NextId(), intoTy, trueCase, falseCase);
            AddTm(tm);
            AddAndVerify(_boolElim, trueCase.Id, falseCase.Id, tm.Id);
            return tm;
        }

        private void AddCtx(Ctx ctx)
        {
            Register(ctx);
            _fix.AddFact(_ctx, ctx.Id);
        }

        private void AddMorph(CtxMorph morph)
        {
            Register(morph);
            _fix.AddFact(_ctxMorph, morph.Domain.Id, morph.Id, morph.Codomain.Id);
        }

        private void AddTy(Ty ty)
        {
            Register(ty);
            _fix.AddFact(_ty, ty.Ctx.Id, ty.Id);
        }

        private void AddTm(Tm tm)
        {
            Register(tm);
            _fix.AddFact(_tmTy, tm.Ctx.Id, tm.Id, tm.Ty.Id);
        }

        private readonly Dictionary<uint, CwfNode> _nodeMap =
            new Dictionary<uint, CwfNode>();

        private void Register(CwfNode node)
        {
            if (!_nodeMap.TryGetValue(node.Id, out CwfNode? oldNode) ||
                // Keep smallest node in map (for easier debugging)
                node.ToString().Length < oldNode.ToString().Length)
            {
                _nodeMap[node.Id] = node;
            }
        }

        private void AddAndVerify(FuncDecl pred, params uint[] args)
        {
            _fix.AddFact(pred, args);
            VerifyDebug();
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
            uint id = ((BitVecNum)expr.Args[1]).UInt;
            return id;
        }

        public void Dump(string rels)
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
            ans = _nodeMap.Aggregate(
                    ans,
                    (acc, kvp) => acc.Replace($"#x{kvp.Key:x8}", "'" + kvp.Value + "'"));
            return ans + Environment.NewLine;
        }

        [Conditional("DEBUG")]
        private void VerifyDebug() => Verify();

        internal void Verify()
        {
            void Check(BoolExpr query)
            {
                if (_fix.Query(query) == Status.UNSATISFIABLE)
                    return;

                Debug.WriteLine("Answer:");
                Debug.WriteLine(ToDebug(_fix.GetAnswer()));
                Debug.WriteLine("");
                Debug.WriteLine("Test:");
                Debug.WriteLine(DebugDump.CreateTest(_nodeMap.Values));

                _fix.Parameters = _z3Ctx.MkParams().Add("datalog.generate_explanations", true);
                _fix.Query(query);
                _fix.Parameters = _z3Ctx.MkParams();
                throw new Exception($"Verification has failed:{Environment.NewLine}{ToDebug(_fix.GetAnswer())}");
            }

            Quantifier typesOfEqTerms = _z3Ctx.MkExists(
                new[] { _M, _N, _G, _D, _s, _t },
                (BoolExpr)_tmEq.Apply(_M, _N) &
                (BoolExpr)_tmTy.Apply(_G, _M, _s) &
                (BoolExpr)_tmTy.Apply(_D, _N, _t) &
                (!(BoolExpr)_tyEq.Apply(_s, _t) |
                 !(BoolExpr)_ctxEq.Apply(_G, _D)));

            Check(typesOfEqTerms);

            Quantifier typesOfEqTypes = _z3Ctx.MkExists(
                new[] { _G, _D, _s, _t },
                (BoolExpr)_tyEq.Apply(_s, _t) &
                (BoolExpr)_ty.Apply(_G, _s) &
                (BoolExpr)_ty.Apply(_D, _t) &
                 !(BoolExpr)_ctxEq.Apply(_G, _D));

            Check(typesOfEqTypes);

            Quantifier compositions = _z3Ctx.MkExists(
                new[] { _g, _f, _gf, _A, _B, _C, _D, _E, _F, },
                (BoolExpr)_comp.Apply(_g, _f, _gf) &
                (BoolExpr)_ctxMorph.Apply(_A, _f, _B) &
                (BoolExpr)_ctxMorph.Apply(_C, _g, _D) &
                (BoolExpr)_ctxMorph.Apply(_E, _gf, _F) &
                (!(BoolExpr)_ctxEq.Apply(_B, _C) |
                 !(BoolExpr)_ctxEq.Apply(_E, _A) |
                 !(BoolExpr)_ctxEq.Apply(_F, _D)));

            Check(compositions);

            Quantifier idMorphs = _z3Ctx.MkExists(
                new[] { _f, _G, _D },
                (BoolExpr)_idMorph.Apply(_f) &
                (BoolExpr)_ctxMorph.Apply(_G, _f, _D) &
                 !(BoolExpr)_ctxEq.Apply(_G, _D));

            Check(idMorphs);

            Quantifier tySubsts = _z3Ctx.MkExists(
                new[] { _s, _t, _G, _D, _f, _A, _B },
                (BoolExpr)_tySubst.Apply(_s, _f, _t) &
                (BoolExpr)_ty.Apply(_G, _s) &
                (BoolExpr)_ty.Apply(_D, _t) &
                (BoolExpr)_ctxMorph.Apply(_A, _f, _B) &
                (!(BoolExpr)_ctxEq.Apply(_B, _G) |
                 !(BoolExpr)_ctxEq.Apply(_A, _D)));

            Check(tySubsts);

            Quantifier tmSubsts = _z3Ctx.MkExists(
                new[] { _M, _N, _G, _D, _s, _t, _f, _A, _B },
                (BoolExpr)_tmSubst.Apply(_M, _f, _N) &
                (BoolExpr)_tmTy.Apply(_G, _M, _s) &
                (BoolExpr)_tmTy.Apply(_D, _N, _t) &
                (BoolExpr)_ctxMorph.Apply(_A, _f, _B) &
                (!(BoolExpr)_ctxEq.Apply(_B, _G) |
                 !(BoolExpr)_ctxEq.Apply(_A, _D)));

            Check(tmSubsts);

            Quantifier projCtxs = _z3Ctx.MkExists(
                new[] { _G, _s, _f, _A, _B },
                (BoolExpr)_projCtx.Apply(_G, _s, _f) &
                (BoolExpr)_ctxMorph.Apply(_A, _f, _B) &
                (!(BoolExpr)_ctxEq.Apply(_B, _G) |
                 !(BoolExpr)_comprehension.Apply(_G, _s, _A)));

            Check(projCtxs);

            Quantifier projTms = _z3Ctx.MkExists(
                new[] { _G, _s, _M, _D, _t },
                (BoolExpr)_projTm.Apply(_G, _s, _M) &
                (BoolExpr)_tmTy.Apply(_D, _M, _t) &
                (!(BoolExpr)_comprehension.Apply(_G, _s, _D)));

            Check(projTms);

            Quantifier extensions = _z3Ctx.MkExists(
                new[] { _f, _M, _g, _G, _D, _A, _B, _C, _s, _t },
                (BoolExpr)_extension.Apply(_f, _M, _g) &
                (BoolExpr)_ctxMorph.Apply(_G, _f, _D) &
                (BoolExpr)_tmTy.Apply(_G, _M, _s) &
                (BoolExpr)_tySubst.Apply(_s, _f, _t) &
                (BoolExpr)_ctxMorph.Apply(_A, _g, _B) &
                (!(BoolExpr)_ctxEq.Apply(_A, _G) |
                 !(BoolExpr)_comprehension.Apply(_D, _t, _B)));

            Check(extensions);

            var projFalse = _z3Ctx.MkExists(
                new[] { _M, _G, _s },
                (BoolExpr)_false.Apply(_M) &
                (BoolExpr)_projTm.Apply(_G, _s, _M));

            Check(projFalse);
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

(rule (=> (and (BoolElim M N O) (TmTy G O s)
               (BoolElim M N P) (TmTy G P s))
          (TmEq O P))
      BoolElim-Functional)

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

; h . (g . f) = (h . g) . f
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
(rule (=> (and (Comp g f gf)
               (TySubst s gf t)
               (TySubst s g u))
          (TySubst u f t))
      Ty-Comp-1)

(rule (=> (and (TySubst s g t)
               (TySubst t f u)
               (Comp g f gf))
          (TySubst s gf u))
      Ty-Comp-2)

; M{id} = M
(rule (=> (and (TmTy G M s)
               (IdMorph f) (CtxMorph G f G))
          (TmSubst M f M))
      Tm-Id)

; M{g . f} = M{g}{f}
(rule (=> (and (Comp g f gf)
               (TmSubst M gf N)
               (TmSubst M g O))
          (TmSubst O f N))
      Tm-Comp-1)

(rule (=> (and (TmSubst M g N)
               (TmSubst N f O)
               (Comp g f gf))
          (TmSubst M gf O))
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

; 〈g, M〉 . f = 〈g . f, M{f}〉
(rule (=> (and (Extension g M e)
               (Comp e f h)
               (Comp g f gf)
               (TmSubst M f N))
          (Extension gf N h))
      Cons-Natural-1)

(rule (=> (and (Comp g f gf)
               (TmSubst M f N)
               (Extension gf N e)
               (Extension g M i))
          (Comp i f e))
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

;;;;;;;;;; Uniqueness rules ;;;;;;;;;;

; Unique morphisms to terminal object
(rule (=> (and (CtxEmpty G)
               (CtxMorph D f G)
               (CtxMorph D g G))
          (CtxMorphEq f g))
      Bang-Unique)

; Unique extension
(rule (=> (and (ProjCtx G s p) (ProjTm G s M)
               (Comp p e f)
               (TmSubst M e N))
          (Extension f N e))
      Extension-Unique)

; O{<1, True>} = M and O{<1, False>} = N implies
; BoolElim M N = O
(rule (=> (and (TmBar P g) (True P)
               (TmBar Q h) (False Q)
               (TmSubst O g M)
               (TmSubst O h N))
          (BoolElim M N O))
      BoolElim-Unique)

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
               (CtxMorph G f D)
               (TySubst t f s))
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

;; True(D){f : G -> D} = True(G)
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

; (BoolElim M N){<f, O>} = (BoolElim M{f} N{f}){<1, O>}
(rule (=> (and (BoolElim M N P)
               (Extension f O e)
               (TmSubst P e Q)
               (TmSubst M f R)
               (TmSubst N f S)
               (BoolElim R S T)
               (TmBar O g))
          (TmSubst T g Q))
      (BoolElim-Stable-1))

(rule (=> (and (BoolElim M N P)
               (Extension f O e)
               (TmSubst P e Q)
               (TmSubst M f R)
               (TmSubst N f S)
               (BoolElim R S T)
               (TmBar O g))
          (TmSubst T g Q))
      (BoolElim-Stable-2))

;; (BoolElim M N){q(f : G -> D, Bool)} = BoolElim M{f} N{f}
;(rule (=> (and (BoolElim M N O)
;               (CtxMorph G f D)
;               (Weakening f s q) (Bool s) (Ty D s)
;               (TmSubst O q P)
;               (TmSubst M f Q)
;               (TmSubst N f R))
;          (BoolElim Q R P))
;      BoolElim-Natural-1)
;
;(rule (=> (and (BoolElim Q R P)
;               (TmSubst M f Q)
;               (TmSubst N f R)
;               (CtxMorph G f D)
;               (BoolElim M N O) 
;               (Weakening f s q) (Bool s) (Ty D s))
;          (TmSubst O q P))
;      BoolElim-Natural-2)

;; (BoolElim M N){<id, True>} = M
;(rule (=> (and (BoolElim M N O) (TmTy D O s) ; if O is bool-elim
;               (TmBar P f) (CtxMorph G f D)  ; and f is P bar
;               (True P))                     ; and P is True
;          (TmSubst O f M))                   ; then the substitution is the true case.
;      BoolElim-True)
;
;; (BoolElim M N){<id, False>} = N
;(rule (=> (and (BoolElim M N O) (TmTy D O s) ; if O is bool-elim
;               (TmBar P f) (CtxMorph G f D)  ; and f is P bar
;               (False P))                    ; and P is False
;          (TmSubst O f N))                   ; then the substitution is the false case.
;      BoolElim-False)

; (BoolElim M N){<f, True>} = M{f}
(rule (=> (and (BoolElim M N O) (TmTy D O s)      ; if O is bool-elim in D
               (Extension f P e) (CtxMorph G e D) ; and e = <f, P> : G -> D
               (TmSubst O e Q)                    ; and Q is O{e}
               (True P))                          ; and P is true
          (TmSubst M f Q))                        ; then the substitution is M{f}
      BoolElim-True)

; (BoolElim M N){<f, False>} = N{f}
(rule (=> (and (BoolElim M N O) (TmTy D O s)      ; if O is bool-elim in D
               (Extension f P e) (CtxMorph G e D) ; and e = <f, P> : G -> D
               (TmSubst O e Q)                    ; and Q is O{e}
               (False P))                         ; and P is false
          (TmSubst N f Q))                        ; then the substitution is M{f}
      BoolElim-False)

".Replace("{SortSize}", SortSize.ToString());
    }
}
