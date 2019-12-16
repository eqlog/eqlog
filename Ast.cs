using System;
using System.Collections.Generic;
using System.Linq;

namespace QT
{
    internal abstract class SyntaxNode
    {
        internal static string FormatCtxExtsWithTy(
                IEnumerable<CtxExt> exts, Expr retTy)
            => string.Concat(exts.Select(e => $"({e}) ")) + ": " + retTy;
    }

    internal class Unit : SyntaxNode
    {
        private readonly List<Def> _defs;

        public Unit(List<Def> defs)
        {
            _defs = defs;
        }

        public IReadOnlyList<Def> Definitions => _defs;

        public override string ToString()
            => string.Join(Environment.NewLine + Environment.NewLine, _defs);
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

        public override string ToString()
        {
            string ctxExtsStr = SyntaxNode.FormatCtxExtsWithTy(_ctxExts, RetTy);
            return $"def {Name} {ctxExtsStr} :={Environment.NewLine}  {Body}";
        }
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

        public override string ToString()
            => $"{Name} : {Type}";
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

        public override string ToString()
            => $"let {Id} : {Type} := {Val} in {Body}";
    }

    internal class IdExpr : Expr
    {
        public IdExpr(string id)
        {
            Id = id;
        }

        public string Id { get; }

        public override string ToString()
            => Id;
    }

    internal class ElimExpr : Expr
    {
        private readonly List<CtxExt> _intoExts;
        private readonly List<ElimCase> _cases;

        public ElimExpr(Expr discriminee, string varName, List<CtxExt> intoExts,
                        Expr intoTy, List<ElimCase> cases)
        {
            Discriminee = discriminee;
            VarName = varName;
            _intoExts = intoExts;
            IntoTy = intoTy;
            _cases = cases;
        }

        public Expr Discriminee { get; }
        public string VarName { get; }
        public IReadOnlyList<CtxExt> IntoExts => _intoExts;
        public Expr IntoTy { get; }
        public IReadOnlyList<ElimCase> Cases => _cases;

        public override string ToString()
        {
            string intoStr = SyntaxNode.FormatCtxExtsWithTy(IntoExts, IntoTy);
            string cases = string.Concat(_cases.Select(c => Environment.NewLine + "| " + c));
            return $"elim {Discriminee} as {VarName} into {intoStr}{cases}";
        }
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

        public override string ToString()
        {
            string extsStr = SyntaxNode.FormatCtxExtsWithTy(CaseExts, CaseTy);
            return $"{extsStr} => {Body}";
        }
    }

    internal class AppExpr : Expr
    {
        public AppExpr(Expr fun, Expr arg)
        {
            Fun = fun;
            Arg = arg;
        }

        public Expr Fun { get; }
        public Expr Arg { get; }

        public override string ToString()
            => $"({Fun} {Arg})";
    }
}
