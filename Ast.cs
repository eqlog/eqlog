using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace QT
{
    internal abstract class SyntaxNode
    {
        public override string ToString()
        {
            StringBuilder sb = new StringBuilder();
            PrettyPrinter.Print(this, sb);
            return sb.ToString();
        }
    }

    internal class Unit : SyntaxNode
    {
        private readonly List<Def> _defs;

        public Unit(List<Def> defs)
        {
            _defs = defs;
        }

        public IReadOnlyList<Def> Definitions => _defs;
    }

    internal class Def : SyntaxNode
    {
        private readonly List<CtxExt> _ctxExts;

        public Def(string name, List<CtxExt> ctxExts, Expr retTy, Expr body)
        {
            Name = name;
            _ctxExts = ctxExts;
            RetTy = retTy;
            Body = body;
        }

        public string Name { get; }
        public IReadOnlyList<CtxExt> CtxExts => _ctxExts;
        public Expr RetTy { get; }
        public Expr Body { get; }
    }

    internal class CtxExt : SyntaxNode
    {
        public CtxExt(string name, Expr type)
        {
            Name = name;
            Type = type;
        }

        public string Name { get; }
        public Expr Type { get; }
    }

    internal abstract class Expr : SyntaxNode
    {
    }

    internal class LetExpr : Expr
    {
        public LetExpr(string id, Expr type, Expr val, Expr body)
        {
            Id = id;
            Type = type;
            Val = val;
            Body = body;
        }

        public string Id { get; }
        public Expr Type { get; }
        public Expr Val { get; }
        public Expr Body { get; }
    }

    internal class IdExpr : Expr
    {
        public IdExpr(string id)
        {
            Id = id;
        }

        public string Id { get; }
    }

    internal class ElimExpr : Expr
    {
        private readonly List<CtxExt> _intoExts;
        private readonly List<ElimCase> _cases;

        public ElimExpr(Expr discriminee, List<CtxExt> intoExts,
                        Expr intoTy, List<ElimCase> cases)
        {
            Discriminee = discriminee;
            _intoExts = intoExts;
            IntoTy = intoTy;
            _cases = cases;
        }

        public Expr Discriminee { get; }
        public IReadOnlyList<CtxExt> IntoExts => _intoExts;
        public Expr IntoTy { get; }
        public IReadOnlyList<ElimCase> Cases => _cases;
    }

    internal class ElimCase : SyntaxNode
    {
        private readonly List<CtxExt> _caseExts;
        public ElimCase(List<CtxExt> caseExts, Expr caseTy, Expr body)
        {
            _caseExts = caseExts;
            CaseTy = caseTy;
            Body = body;
        }

        public IReadOnlyList<CtxExt> CaseExts => _caseExts;
        public Expr CaseTy { get; }
        public Expr Body { get; }
    }

    internal class AppExpr : Expr
    {
        private readonly List<Expr> _args;
        public AppExpr(string id, List<Expr> args)
        {
            Fun = id;
            _args = args;
        }

        public string Fun { get; }
        public IReadOnlyList<Expr> Args => _args;
    }
}
