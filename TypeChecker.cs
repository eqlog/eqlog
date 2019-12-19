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

        private readonly FuncDecl _tm;
        private readonly FuncDecl _tmEq;

        private readonly FuncDecl _tmTy;

        private readonly FuncDecl _id;

        private readonly Dictionary<string, FuncDecl> _rels;

        private uint _counter;
        private uint NextId() => checked(++_counter);

        private ImmutableDictionary<string, uint> _context = ImmutableDictionary.Create<string, uint>();

        private static readonly string s_z3Setup = $@"
(define-sort TyS () (_ BitVec {SortSize}))
(define-sort TmS () (_ BitVec {SortSize}))
(declare-rel Ty (TyS))
(declare-rel TyEq (TyS TyS))

(declare-rel Tm (TmS))
(declare-rel TmEq (TmS TmS))

(declare-rel TmTy (TmS TyS))

(declare-rel Id (TmS TmS TyS))

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

(rule (=> (Ty s) (TyEq s s)) TyEq-Reflexive)
(rule (=> (TyEq s t) (TyEq t s)) TyEq-Symmetric)
(rule (=> (and (TyEq s t) (TyEq t r)) (TyEq s r)) TyEq-Transitive)

(rule (=> (Tm M) (TmEq M M)) TmEq-Reflexive)
(rule (=> (TmEq M N) (TmEq N M)) TmEq-Symmetric)
(rule (=> (and (TmEq M N) (TmEq N O)) (TmEq M O)) TmEq-Transitive)

(rule (=> (and (TmTy M s) (TyEq s t)) (TmTy M t)) Tm-Conv)

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
            _tm = _rels["Tm"];
            _tmEq = _rels["TmEq"];
            _tmTy = _rels["TmTy"];
            _id = _rels["Id"];

            uint nat = NextId();
            _fix.AddFact(_ty, nat);
            _context = _context.Add("nat", nat);

            uint zero = NextId();
            _fix.AddFact(_tm, zero);
            _fix.AddFact(_tmTy, zero, nat);
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
            _fix.AddFact(_tm, reflId);
            _fix.AddFact(_tmTy, reflId, idId);
            return reflId;
        }

        public uint TypeCheck(Def def)
        {
            ImmutableDictionary<string, uint> old = _context;
            foreach (CtxExt ctxExt in def.CtxExts)
            {
                uint typeId = TypeCheckType(ctxExt.Type);
                uint varId = NextId();
                _fix.AddFact(_tm, varId);
                _fix.AddFact(_tmTy, varId, typeId);
                DefId(ctxExt.Name, varId);
            }

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
                    throw new Exception("Invalid function to apply " + app.Fun);
                default:
                    throw new Exception("Cannot handle yet");
            }
        }

        private BitVecNum BV(uint id) => _ctx.MkBV(id, SortSize);

        public void Dispose()
        {
            _ctx.Dispose();
        }
    }
}
