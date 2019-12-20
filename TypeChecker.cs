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
        private const int SortSize = 32;

        private readonly Context _ctx;
        private readonly Fixedpoint _fix;

        private readonly BitVecSort _sort;

        private readonly FuncDecl _ty;
        private readonly FuncDecl _tyEq;

        private readonly FuncDecl _tmEq;

        private readonly FuncDecl _tmTy;

        private readonly FuncDecl _id;

        private readonly FuncDecl _zero;
        private readonly FuncDecl _succ;
        private readonly FuncDecl _elimNat;

        private readonly Dictionary<string, FuncDecl> _rels;

        private uint _counter;
        private uint NextId() => checked(++_counter);

        private ImmutableDictionary<string, uint> _context = ImmutableDictionary.Create<string, uint>();

        private static readonly string s_z3Setup = $@"
(define-sort TyS () (_ BitVec {SortSize}))
(define-sort TmS () (_ BitVec {SortSize}))
(declare-rel Ty (TyS))
(declare-rel TyEq (TyS TyS))

(declare-rel TmEq (TmS TmS))

(declare-rel TmTy (TmS TyS))

(declare-rel Id (TmS TmS TyS))

; Zero O -- O is a zero
(declare-rel Zero (TmS))
; Succ A B -- B is S A
(declare-rel Succ (TmS TmS))
; ElimNat N CO P CS X
; X is the elimination of N with zero-case CO
; and succ-case [P:nat]CS
(declare-rel ElimNat (TmS TmS TmS TmS TmS))

(declare-var s TyS)
(declare-var t TyS)
(declare-var r TyS)
(declare-var p TyS)
(declare-var q TyS)

(declare-var M TmS)
(declare-var N TmS)
(declare-var O TmS)
(declare-var P TmS)
(declare-var Q TmS)
(declare-var CO TmS)
(declare-var CS TmS)

(rule (=> (Ty s) (TyEq s s)) TyEq-Reflexive)
(rule (=> (TyEq s t) (TyEq t s)) TyEq-Symmetric)
(rule (=> (and (TyEq s t) (TyEq t r)) (TyEq s r)) TyEq-Transitive)

(rule (=> (TmTy M s) (TmEq M M)) TmEq-Reflexive)
(rule (=> (TmEq M N) (TmEq N M)) TmEq-Symmetric)
(rule (=> (and (TmEq M N) (TmEq N O)) (TmEq M O)) TmEq-Transitive)

(rule (=> (and (TmTy M s) (TyEq s t)) (TmTy M t)) Tm-Conv)

(rule (=> (and (and (TmTy M s)
                    (TmTy N t))
               (TmEq M N))
          (TyEq s t))
      TmTy-Congr)

(rule (=> (and (and (Id M N s)
                    (Id O P t))
               (and (TmEq M O)
                    (TmEq N P)))
          (TyEq s t))
      Id-WellDefined)

(rule (=> (and (Id M N s) (TmTy O s))
          (TmEq M N))
      Id-Reflection)

(rule (=> (and (Id M N s)
               (and (TmTy P s)
                    (TmTy Q s)))
          (TmEq P Q))
      Id-Eq)

(rule (=> (and (Zero M)
               (Zero N))
          (TmEq M N))
      Zero-Eq)

(rule (=> (and (and (Succ M N)
                    (Succ O P))
               (TmEq M O))
          (TmEq N P))
      Succ-WellDefined)

(rule (=> (and (Succ M N)
               (TmEq O N))
          (Succ M O))
      Succ-Eq)

(rule (=> (and (and (Succ M N)
                    (Succ O P))
               (TmEq N P))
          (TmEq M O))
      Succ-Injective)

(rule (=> (and (ElimNat M CO P CS O)
               (Zero M))
          (TmEq O CO))
      ElimNat-O)

(rule (=> (and (ElimNat M CO P CS O)
               (Succ N M))
          (TmEq O CS))
      ElimNat-S1)

(rule (=> (and (ElimNat M CO P CS O)
               (Succ N M))
          (TmEq P N))
      ElimNat-S2)
";

        public TypeChecker()
        {
            _ctx = new Context();
            _fix = _ctx.MkFixedpoint();
            _fix.Parameters =
                _ctx.MkParams()
                .Add("fp.engine", "datalog")
                .Add("datalog.generate_explanations", true);
            _fix.ParseString(s_z3Setup);
            _sort = _ctx.MkBitVecSort(SortSize);

            _rels = CollectRelations(_fix.Rules);
            _ty = _rels["Ty"];
            _tyEq = _rels["TyEq"];
            _tmEq = _rels["TmEq"];
            _tmTy = _rels["TmTy"];
            _id = _rels["Id"];
            _zero = _rels["Zero"];
            _succ = _rels["Succ"];
            _elimNat = _rels["ElimNat"];

            uint nat = NextId();
            _fix.AddFact(_ty, nat);
            _context = _context.Add("nat", nat);

            uint zero = NextId();
            _fix.AddFact(_tmTy, zero, nat);
            _fix.AddFact(_zero, zero);
            _context = _context.Add("O", zero);
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

        private uint FormId(uint tmLeft, uint tmRight)
        {
            Z3Expr s = _ctx.MkConst("σ", _sort);
            Status status =
                _fix.Query(
                    _ctx.MkExists(
                        new[] { s },
                        (BoolExpr)_tmTy.Apply(BV(tmLeft), s) &
                        (BoolExpr)_tmTy.Apply(BV(tmRight), s)));

            if (status != Status.SATISFIABLE)
            {
                throw new Exception("Cannot form id type");
            }

            uint id = NextId();
            _fix.AddFact(_ty, id);
            _fix.AddFact(_id, tmLeft, tmRight, id);

            return id;
        }

        private uint IntroduceId(uint tm)
        {
            uint idId = FormId(tm, tm);
            uint reflId = NextId();
            _fix.AddFact(_tmTy, reflId, idId);
            return reflId;
        }

        private uint IntroduceSucc(uint arg)
        {
            if (_fix.Query((BoolExpr)_tmTy.Apply(BV(arg), BV(_context["nat"]))) != Status.SATISFIABLE)
                throw new Exception("Expected arg to constructor S to be of type nat");

            uint succId = NextId();
            _fix.AddFact(_tmTy, succId, _context["nat"]);
            _fix.AddFact(_succ, arg, succId);
            return succId;
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
                DefId(def.Name, bodyId);
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
                case ElimExpr elim:
                    uint discrimineeId = TypeCheck(elim.Discriminee);
                    if (_fix.Query((BoolExpr)_tmTy.Apply(BV(discrimineeId), BV(_context["nat"]))) == Status.SATISFIABLE)
                        return ElimNat(elim, discrimineeId);

                    throw new Exception($"Cannot eliminate {elim.Discriminee} since it is not of type nat");

                case IdExpr id:
                    return _context[id.Id];
                case AppExpr app:
                    if (app.Fun == "id")
                        return FormId(TypeCheck(app.Args[0]), TypeCheck(app.Args[1]));
                    if (app.Fun == "refl")
                        return IntroduceId(TypeCheck(app.Args.Single()));
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
                    if (app.Fun == "S")
                        return IntroduceSucc(TypeCheck(app.Args.Single()));

                    throw new Exception("Invalid function to apply " + app.Fun);
                default:
                    throw new Exception("Cannot handle yet");
            }
        }

        private uint ElimNat(ElimExpr elim, uint discriminee)
        {
            if (elim.IntoExts.Count != 1)
                throw new Exception($"Invalid context extension {string.Join(" ", elim.IntoExts)}");

            if (elim.Cases.Count != 2)
                throw new Exception($"Expected 2 cases for nat elimination");

            if (elim.Cases[0].CaseExts.Count != 0)
                throw new Exception($"{elim.Cases[0]}: expected no context extensions");

            if (elim.Cases[1].CaseExts.Count != 2)
                throw new Exception($"{elim.Cases[1]}: expected 2 context extensions");

            ImmutableDictionary<string, uint> old = _context;
            (_, uint intoCtxTyId) = ExtendContext(elim.IntoExts[0]);
            if (_fix.Query((BoolExpr)_tyEq.Apply(BV(intoCtxTyId), BV(_context["nat"]))) != Status.SATISFIABLE)
                throw new Exception($"Invalid context extension {elim.IntoExts[0]}, expected type nat");

            TypeCheckType(elim.IntoTy);
            _context = old;

            ElimCase zeroCase = elim.Cases[0];
            Expr zeroCaseExpectedTy = Subst(elim.IntoTy, elim.IntoExts, new[] { new IdExpr("O") });
            uint zeroCaseExpectedTyId = TypeCheckType(zeroCaseExpectedTy);
            uint zeroCaseId = TypeCheck(zeroCase.Body);
            if (_fix.Query((BoolExpr)_tmTy.Apply(BV(zeroCaseId), BV(zeroCaseExpectedTyId))) != Status.SATISFIABLE)
                throw new Exception($"{zeroCase.Body}: Invalid type of 0 case, expected {zeroCaseExpectedTy}");

            ElimCase succCase = elim.Cases[1];
            (uint predId, uint predTyId) = ExtendContext(succCase.CaseExts[0]);
            if (_fix.Query((BoolExpr)_tyEq.Apply(BV(predTyId), BV(_context["nat"]))) != Status.SATISFIABLE)
                throw new Exception($"Invalid context extension {succCase.CaseExts[0]}, expected type nat");

            (uint ihId, uint ihTyId) = ExtendContext(succCase.CaseExts[1]);
            Expr expectedTy = Subst(elim.IntoTy, new[] { elim.IntoExts[0] }, new[] { new IdExpr(succCase.CaseExts[0].Name.Name) });
            uint expectedTyId = TypeCheckType(expectedTy);
            if (_fix.Query((BoolExpr)_tyEq.Apply(BV(ihTyId), BV(expectedTyId))) != Status.SATISFIABLE)
                throw new Exception($"IH has type {succCase.CaseExts[1]} which does not match specified into-type {expectedTy}");

            Expr succCaseExpectedTy = Subst(elim.IntoTy, elim.IntoExts, new[] { new AppExpr("S", new List<Expr> { new IdExpr(succCase.CaseExts[0].Name.Name) }) });
            uint succCaseExpectedTyId = TypeCheckType(succCaseExpectedTy);
            uint succCaseId = TypeCheck(succCase.Body);
            if (_fix.Query((BoolExpr)_tmTy.Apply(BV(succCaseId), BV(succCaseExpectedTyId))) != Status.SATISFIABLE)
                throw new Exception($"{succCase.Body}: Invalid type of succ case, expected {succCaseExpectedTy}");

            _context = old;

            Expr finalTy = Subst(elim.IntoTy, elim.IntoExts, new[] { elim.Discriminee });
            uint finalTyId = TypeCheckType(finalTy);

            uint elimId = NextId();
            _fix.AddFact(_tmTy, elimId, finalTyId);
            _fix.AddFact(_elimNat, discriminee, zeroCaseId, predId, succCaseId, elimId);
            return elimId;
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
