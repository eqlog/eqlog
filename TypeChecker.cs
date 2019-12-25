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

        private readonly Context _ctx;
        private readonly Fixedpoint _fix;

        private readonly FuncDecl _con;
        private readonly FuncDecl _ty;
        private readonly FuncDecl _tmTy;
        private readonly FuncDecl _conEq;
        private readonly FuncDecl _tyEq;
        private readonly FuncDecl _tmEq;
        private readonly FuncDecl _conEmpty;
        private readonly FuncDecl _comprehension;

        private readonly Dictionary<string, FuncDecl> _rels;

        private uint _counter;
        private uint NextId() => checked(++_counter);

        private ImmutableDictionary<string, uint> _context = ImmutableDictionary.Create<string, uint>();
        private readonly Dictionary<string, Def> _globals = new Dictionary<string, Def>();

        private static readonly string s_z3Setup = @"
(define-sort ConS () (_ BitVec {SortSize}))
(define-sort ConMorphS () (_ BitVec {SortSize}))
(define-sort TyS () (_ BitVec {SortSize}))
(define-sort TmS () (_ BitVec {SortSize}))

; ConEq G D -- |- G = D ctx
(declare-rel ConEq (ConS ConS))
; ConMorphEq f g -- G |- f = g => D
(declare-rel ConMorphEq (ConMorphS ConMorphS))
; TyEq s t -- G |- s = t type
(declare-rel TyEq (TyS TyS))
; TmEq M N -- G |- M = N : s
(declare-rel TmEq (TmS TmS))

; Con G -- |- G ctx
(declare-rel Con (ConS))
; ConMorph G f D -- G |- f => D
(declare-rel ConMorph (ConS ConMorphS ConS))
; Comp g f h -- h is g . f
(declare-rel Comp (ConMorphS ConMorphS ConMorphS))
; Ty G s -- G |- s type
(declare-rel Ty (ConS TyS))
; TmTy G M s -- G |- M : s
(declare-rel TmTy (ConS TmS TyS))

; Functional relations
; IdMorph G f -- f is the identity context morphism for G
(declare-rel IdMorph (ConS ConMorphS))
; TySubst s f t -- t is s{f}
(declare-rel TySubst (TyS ConMorphS TyS))
; TmSubst M f N -- N is M{f}
(declare-rel TmSubst (TmS ConMorphS TmS))
; ConEmpty G -- G is the empty (terminal) context
(declare-rel ConEmpty (ConS))
; Comprehension G s D -- |- G, x : s = D ctx
(declare-rel Comprehension (ConS TyS ConS))
; ProjCon G s f -- f is the projection G, x : s |- p(s) => G
(declare-rel ProjCon (ConS TyS ConMorphS))
; ProjTm G s M -- M is the projection G, x : s |- x : s
(declare-rel ProjTm (ConS TyS TmS))
; Extension f M g -- g = 〈f, M〉
(declare-rel Extension (ConMorphS TmS ConMorphS))

(declare-var A ConS)
(declare-var B ConS)
(declare-var C ConS)
(declare-var D ConS)
(declare-var E ConS)
(declare-var F ConS)
(declare-var G ConS)

(declare-var e ConMorphS)
(declare-var f ConMorphS)
(declare-var g ConMorphS)
(declare-var h ConMorphS)
(declare-var i ConMorphS)
(declare-var j ConMorphS)
(declare-var k ConMorphS)
(declare-var p ConMorphS)
(declare-var q ConMorphS)

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
(declare-var CO TmS)
(declare-var CS TmS)

;;;;;;;;;; Equalities ;;;;;;;;;;

; ConEq is an equivalence relation
(rule (=> (Con G) (ConEq G G)) ConEq-Reflexive)
(rule (=> (ConEq G D) (ConEq D G)) ConEq-Symmetric)
(rule (=> (and (ConEq G D) (ConEq D B)) (ConEq G B)) ConEq-Transitive)

; ConMorphEq is an equivalence relation
(rule (=> (ConMorph G f D) (ConMorphEq f f)) ConMorphEq-Reflexive)
(rule (=> (ConMorphEq f g) (ConMorphEq g f)) ConMorphEq-Symmetric)
(rule (=> (and (ConMorphEq f g)
               (ConMorphEq g h))
          (ConMorphEq f h))
      ConMorphEq-Transitive)

; TyEq is an equivalence relation
(rule (=> (Ty G s) (TyEq s s)) TyEq-Reflexive)
(rule (=> (TyEq s t) (TyEq t s)) TyEq-Symmetric)
(rule (=> (and (TyEq s t) (TyEq t r)) (TyEq s r)) TyEq-Transitive)

; TmEq is an equivalence relation
(rule (=> (TmTy G M s) (TmEq M M)) TmEq-Reflexive)
(rule (=> (TmEq M N) (TmEq N M)) TmEq-Symmetric)
(rule (=> (and (TmEq M N) (TmEq N O)) (TmEq M O)) TmEq-Transitive)

;;;;;;;;;; Congruence rules ;;;;;;;;;;

; ConMorph
(rule (=> (and (and (and (ConMorph G f D)
                         (ConEq G A))
                    (ConMorphEq f g))
               (ConEq D B))
          (ConMorph A g B))
      ConMorph-Congr)

; Comp
(rule (=> (and (and (and (Comp f g h)
                         (ConMorphEq f i))
                    (ConMorphEq g j))
               (ConMorphEq h k))
          (Comp i j k))
      Comp-Congr)

; Ty
(rule (=> (and (Ty G s)
               (ConEq G D))
          (Ty D s))
      Ty-Conv)

; TmTy
(rule (=> (and (and (TmTy G M s)
                    (ConEq G D))
               (TyEq s t))
          (TmTy D M t))
      Tm-Conv)

; IdMorph
(rule (=> (and (and (IdMorph G f)
                    (ConEq G D))
               (ConMorphEq f g))
          (IdMorph D g))
      IdMorph-Congr)

; TySubst
(rule (=> (and (and (and (TySubst s f t)
                         (TyEq s u))
                    (ConMorphEq f g))
               (ConMorphEq t v))
          (TySubst u g v))
      TySubst-Congr)

; TmSubst
(rule (=> (and (and (and (TmSubst M f N)
                         (TmEq M O))
                    (ConMorphEq f g))
               (TmEq N P))
          (TmSubst O g P))
      TmSubst-Congr)

; ConEmpty
(rule (=> (and (ConEmpty G)
               (ConEq G D))
          (ConEmpty D))
      ConEmpty-Congr)

; Comprehension
(rule (=> (and (and (and (Comprehension G s A)
                         (ConEq G D))
                    (TyEq s t))
               (ConEq A B))
          (Comprehension D t B))
      Comprehension-Congr)

; ProjCon
(rule (=> (and (and (and (ProjCon G s f)
                         (ConEq G D))
                    (TyEq s t))
               (ConMorphEq f g))
          (ProjCon D t g))
      ProjCon-Congr)

; ProjTm
(rule (=> (and (and (and (ProjTm G s M)
                         (ConEq G D))
                    (TyEq s t))
               (TmEq M N))
          (ProjTm D t N))
      ProjTm-Congr)

; Extension
(rule (=> (and (and (and (Extension f M g)
                         (ConMorphEq f h))
                    (TmEq M N))
               (ConMorphEq g i))
          (Extension h N i))
      Extension-Congr)

;;;;;;;;;; Functionality rules ;;;;;;;;;;

(rule (=> (and (IdMorph G f)
               (IdMorph G g))
          (ConMorphEq f g))
      IdMorph-Functional)

(rule (=> (and (TySubst s f t)
               (TySubst s f u))
          (TyEq t u))
      TySubst-Functional)

(rule (=> (and (TmSubst M f N)
               (TmSubst M f O))
          (TmEq N O))
      TmSubst-Functional)

(rule (=> (and (ConEmpty G) (ConEmpty D))
          (ConEq G D))
      ConEmpty-Functional)

(rule (=> (and (Comprehension G s D)
               (Comprehension G s A))
          (ConEq D A))
      Comprehension-Functional)

(rule (=> (and (ProjCon G s f)
               (ProjCon G s g))
          (ConMorphEq f g))
      ProjCon-Functional)

(rule (=> (and (ProjTm G s M)
               (ProjTm G s N))
          (TmEq M N))
      ProjTm-Functional)

(rule (=> (and (Extension f M g)
               (Extension f M h))
          (ConMorphEq g h))
      Extension-Functional)

;;;;;;;;;; Categorical rules ;;;;;;;;;;

; s{id} = s
(rule (=> (and (TySubst s f t)
               (IdMorph G f))
          (TyEq s t))
      Ty-Id)

; s{g . f} = s{g}{f}
(rule (=> (and (and (Comp g f h)
                    (TySubst s h t))
               (and (TySubst s g u)
                    (TySubst u f v)))
          (TyEq t v))
      Ty-Comp)

; M{id} = M
(rule (=> (and (TmSubst M f N)
               (IdMorph G f))
          (TmEq M N))
      Tm-Id)

; M{g . f} = M{g}{f}
(rule (=> (and (and (Comp g f h)
                    (TmSubst M h N))
               (and (TmSubst M g O)
                    (TmSubst O f P)))
          (TmEq N P))
      Tm-Comp)

; p(s) . 〈f, M〉= f
(rule (=> (and (and (ProjCon G s p)
                    (Extension f M e))
               (Comp p e g))
          (ConMorphEq g f))
      Cons-L)

; M = v /\ 〈f, N〉= e /\ M{e} = O => O = N
(rule (=> (and (and (ProjTm G s M)
                    (Extension f N e))
               (TmSubst M e O))
          (TmEq O N))
      Cons-R)

; 〈f, M〉. g = 〈f . g, M{g}〉
; 〈f, M〉 = e /\ e . g = h /\ f . g = i /\ M{g} = N /\ 〈i, N〉= j
; => h = j
(rule (=> (and (and (and (and (Extension f M e)
                              (Comp e g h))
                         (Comp f g i))
                    (TmSubst M g N))
               (Extension i N j))
          (ConMorphEq h j))
      Cons-Nat)

; 〈p(s), v〉= id
; p(s) = p /\ M = v /\ 〈p, M〉= e /\ id = f => e = f
(rule (=> (and (and (and (and (ProjCon G s p)
                              (ProjTm G s M))
                         (Extension p M e))
                    (Comprehension G s D))
               (IdMorph D f))
          (ConMorphEq e f))
      Cons-Id)

;;;;;;;;;; Type forming/introduction/elimination ;;;;;;;;;;

;(rule (=> (and (and (Id M N s)
;                    (Id O P t))
;               (and (TmEq M O)
;                    (TmEq N P)))
;          (TyEq s t))
;      Id-WellDefined)
;
;(rule (=> (and (Id M N s) (TmTy O s))
;          (TmEq M N))
;      Id-Reflection)
;
;(rule (=> (and (Id M N s)
;               (and (TmTy P s)
;                    (TmTy Q s)))
;          (TmEq P Q))
;      Id-Eq)
;
;(rule (=> (and (Zero M)
;               (Zero N))
;          (TmEq M N))
;      Zero-Eq)
;
;(rule (=> (and (and (Succ M N)
;                    (Succ O P))
;               (TmEq M O))
;          (TmEq N P))
;      Succ-WellDefined)
;
;(rule (=> (and (Succ M N)
;               (TmEq O N))
;          (Succ M O))
;      Succ-Eq)
;
;(rule (=> (and (and (Succ M N)
;                    (Succ O P))
;               (TmEq N P))
;          (TmEq M O))
;      Succ-Injective)
;
;(rule (=> (and (ElimNat M CO P CS O)
;               (Zero M))
;          (TmEq O CO))
;      ElimNat-O)
;
;(rule (=> (and (ElimNat M CO P CS O)
;               (Succ N M))
;          (TmEq O CS))
;      ElimNat-S1)
;
;(rule (=> (and (ElimNat M CO P CS O)
;               (Succ N M))
;          (TmEq P N))
;      ElimNat-S2)
".Replace("{SortSize}", SortSize.ToString());

        public TypeChecker()
        {
            _ctx = new Context();
            _fix = _ctx.MkFixedpoint();
            _fix.Parameters =
                _ctx.MkParams()
                .Add("fp.engine", "datalog")
                .Add("datalog.generate_explanations", true);
            _fix.ParseString(s_z3Setup);

            _rels = CollectRelations(_fix.Rules);
            _con = _rels["Con"];
            _ty = _rels["Ty"];
            _tmTy = _rels["TmTy"];
            _conEq = _rels["ConEq"];
            _tyEq = _rels["TyEq"];
            _tmEq = _rels["TmEq"];
            _conEmpty = _rels["ConEmpty"];
            _comprehension = _rels["Comprehension"];
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

        public uint TypeCheck(Def def)
        {
            ImmutableDictionary<string, uint> old = _context;
            foreach (CtxExt ctxExt in def.CtxExts)
                ExtendContext(ctxExt);

            uint resultTypeId = TypeCheckType(def.RetTy);
            uint bodyId = TypeCheck(def.Body);
            if (_fix.Query((BoolExpr)_tmTy.Apply(BV(bodyId), BV(resultTypeId))) == Status.SATISFIABLE)
            {
                _context = old;
                _globals[def.Name.Name] = def;
                return bodyId;
            }

            throw new Exception($"{def.Name}: Body does not type check to {def.RetTy}");
        }

        private (uint typeId, uint varId) ExtendContext(CtxExt ctxExt)
        {
            uint typeId = TypeCheckType(ctxExt.Type);
            uint varId = NextId();
            _fix.AddFact(_tmTy, varId, typeId);
            DefId(ctxExt.Name, varId);
            return (varId, typeId);
        }

        private void DefId(DefId defId, uint val)
        {
            if (!defId.IsDiscard)
                _context = _context.SetItem(defId.Name, val);
        }

        private uint TypeCheckType(Expr expr)
        {
            uint id = TypeCheck(expr);
            if (_fix.Query((BoolExpr)_ty.Apply(BV(id))) == Status.SATISFIABLE)
                return id;

            throw new Exception($"Expected type, got {expr}");
        }

        private uint TypeCheck(Expr expr)
        {
            switch (expr)
            {
                case LetExpr let:
                    uint letValTyId = TypeCheckType(let.Type);
                    uint letValId = TypeCheck(let.Val);
                    if (_fix.Query((BoolExpr)_tmTy.Apply(BV(letValId), BV(letValTyId))) != Status.SATISFIABLE)
                    {
                        throw new Exception(
                                $"let {let.Name}: " +
                                $"Body does not type check to {let.Type}");
                    }

                    ImmutableDictionary<string, uint> old = _context;
                    DefId(let.Name, letValId);
                    uint bodyId = TypeCheck(let.Body);
                    _context = old;
                    return bodyId;
                case IdExpr id:
                    return _context[id.Id];
                case AppExpr app:
                    if (app.Fun == "dump")
                    {
                        uint result = TypeCheck(app.Args[1]);
                        string rel = ((IdExpr)app.Args[0]).Id;
                        _fix.Query(_rels[rel]);
                        string ans = _fix.GetAnswer().ToString();
                        ans = _context.Aggregate(
                                ans,
                                (acc, kvp) => acc = acc.Replace($"#x{kvp.Value:x8}", kvp.Key));
                        Console.WriteLine("------- {0} -------", rel);
                        Console.WriteLine(ans);
                        return result;
                    }
                    if (_globals.TryGetValue(app.Fun, out Def? global))
                    {
                        if (global.CtxExts.Count != app.Args.Count)
                        {
                            string msg =
                                $"Expected {global.CtxExts.Count} arguments " +
                                $"to {app.Fun}";
                            throw new Exception(msg);
                        }

                        Expr newBody = Subst(global.Body, global.CtxExts, app.Args);
                        Console.WriteLine("{0}: {1}", app, newBody);
                        return TypeCheck(newBody);
                    }

                    throw new Exception("Invalid function to apply " + app.Fun);
                default:
                    throw new Exception("Cannot handle yet");
            }
        }

        private BitVecNum BV(uint id) => _ctx.MkBV(id, SortSize);

        private Expr Subst(Expr expr, IReadOnlyList<CtxExt> exts, IReadOnlyList<Expr> replacements)
        {
            int numRenamed = 0;
            Dictionary<string, Expr> repMap = new Dictionary<string, Expr>();
            foreach ((CtxExt ctxExt, Expr rep) in exts.Zip(replacements))
            {
                if (!ctxExt.Name.IsDiscard)
                    repMap[ctxExt.Name.Name] = rep;
            }

            var repBinds = ImmutableDictionary.Create<string, Expr>();

            return Go(expr);

            DefId GoDef(DefId name)
            {
                DefId newName = name;
                if (!name.IsDiscard)
                {
                    newName = new DefId($"${numRenamed++}", false);
                    repBinds = repBinds.SetItem(name.Name, new IdExpr(newName.Name));
                }

                return newName;
            }

            List<CtxExt> GoCtxExts(IEnumerable<CtxExt> exts)
            {
                List<CtxExt> newExts = new List<CtxExt>();
                foreach (CtxExt ext in exts)
                {
                    Expr newType = Go(ext.Type);
                    DefId newName = GoDef(ext.Name);
                    newExts.Add(new CtxExt(newName, newType));
                }

                return newExts;
            }

            Expr Go(Expr e)
            {
                ImmutableDictionary<string, Expr> old;
                DefId newName;
                Expr newBody;
                switch (e)
                {
                    case LetExpr { Name: var name, Type: var type, Val: var val, Body: var body }:
                        Expr newTy = Go(type);
                        Expr newVal = Go(val);

                        old = repBinds;
                        newName = GoDef(name);
                        newBody = Go(body);
                        repBinds = old;
                        return new LetExpr(newName, newTy, newVal, newBody);
                    case IdExpr { Id: var id }:
                        if (repBinds.TryGetValue(id, out Expr repExpr))
                            return repExpr;

                        if (repMap.TryGetValue(id, out repExpr!))
                            return repExpr;

                        return e;
                    case ElimExpr { Discriminee: var disc, IntoExts: var intoExts, IntoTy: var intoTy, Cases: var cases }:
                        Expr newDisc = Go(disc);

                        old = repBinds;

                        List<CtxExt> newIntoExts = GoCtxExts(intoExts);
                        Expr newIntoTy = Go(intoTy);
                        repBinds = old;

                        List<ElimCase> newCases = new List<ElimCase>();
                        foreach (ElimCase @case in cases)
                        {
                            List<CtxExt> newCaseExts = GoCtxExts(@case.CaseExts);
                            newBody = Go(@case.Body);
                            repBinds = old;

                            newCases.Add(new ElimCase(newCaseExts, newBody));
                        }

                        return new ElimExpr(newDisc, newIntoExts, newIntoTy, newCases);
                    case AppExpr { Fun: var fun, Args: var args }:
                        return new AppExpr(fun, args.Select(Go).ToList());
                    default:
                        throw new Exception("Unhandled");
                }
            }
        }

        public void Dispose()
        {
            _ctx.Dispose();
        }
    }
}
