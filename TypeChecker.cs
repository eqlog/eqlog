using Microsoft.Z3;
using System;
using System.Collections.Generic;
using QT.Parse;
using Z3Expr = Microsoft.Z3.Expr;

namespace QT
{
    internal class TypeChecker : IDisposable
    {
        private readonly Context _ctx;
        private readonly Fixedpoint _fix;
        private readonly Dictionary<string, int> _context =
            new Dictionary<string, int>();
        private readonly FuncDecl _isTy;
        private readonly FuncDecl _isTm;
        private readonly FuncDecl _tyEq;
        private readonly FuncDecl _tmTy;
        private readonly FuncDecl _tmEq;

        const string Z3Setup = @"
(define-sort Ty () (_ BitVec 32))
(define-sort Tm () (_ BitVec 32))
(declare-rel IsTy (Ty))
(declare-rel IsTm (Tm))
(declare-rel TyEq (Ty Ty))
(declare-rel TmTy (Tm Ty))
(declare-rel TmEq (Tm Tm))

(declare-var s Ty)
(declare-var t Ty)
(declare-var r Ty)
(rule (=> (IsTy s) (TyEq s s)) TyEq-Reflexive)
(rule (=> (TyEq s t) (TyEq t s)) TyEq-Symmetric)
(rule (=> (and (TyEq s t) (TyEq t r)) (TyEq s r)) TyEq-Transitive)

(declare-var M Tm)
(declare-var N Tm)
(declare-var O Tm)
(rule (=> (IsTm M) (TmEq M M)) TmEq-Reflexive)
(rule (=> (TmEq M N) (TmEq N M)) TmEq-Symmetric)
(rule (=> (and (TmEq M N) (TmEq N O)) (TmEq M O)) TmEq-Transitive)

(rule (=> (and (TmTy M s) (TyEq s t)) (TmTy M t)) Tm-Conv)
";

        public TypeChecker()
        {
            _ctx = new Context();
            _fix = _ctx.MkFixedpoint();
            _fix.Parameters =
                _ctx.MkParams()
                .Add("fp.engine", "datalog")
                .Add("datalog.generate_explanations", true);
            _fix.ParseString(Z3Setup);
            Dictionary<string, FuncDecl> decls = CollectRelations(_fix.Rules);
            _isTy = decls["IsTy"];
            _isTm = decls["IsTm"];
            _tyEq = decls["TyEq"];
            _tmTy = decls["TmTy"];
            _tmEq = decls["TmEq"];

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

            ////Console.WriteLine(_fix.Query(_ctx.MkExists(new[]{x}, _isTy.Apply(x))));

            ////Console.WriteLine(string.Join(Environment.NewLine, (object[])rels));

            //_context.Add("bool", Type("bool"));
            //_context.Add("nat", Type("nat"));
            //_context.Add("O", Axiom("nat"));
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
