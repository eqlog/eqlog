using Antlr4.Runtime.Misc;
using Antlr4.Runtime.Tree;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

namespace QT.Parse
{
    internal class ToAstVisitor : IQtVisitor<SyntaxNode>
    {
        public SyntaxNode Visit(IParseTree tree)
            => throw new NotSupportedException();

        public SyntaxNode VisitArgExpr([NotNull] QtParser.ArgExprContext context)
        {
            if (context.parenthesized != null)
                return context.parenthesized.Accept(this);

            return context.id.Accept(this);
        }

        public SyntaxNode VisitChildren(IRuleNode node)
            => throw new NotSupportedException();

        private List<CtxExt> ParseCtxExts(IEnumerable<QtParser.CtxExtContext> ctxs)
        {
            IEnumerable<CtxExt> MakeExts(QtParser.CtxExtContext ctx)
            {
                Expr ty = (Expr)ctx.ty.Accept(this);
                return ctx._names.Select(id => new CtxExt(id.Text, ty));
            }
            List<CtxExt> l = ctxs.SelectMany(MakeExts).ToList();
            return l;
        }

        public SyntaxNode VisitCtxExt([NotNull] QtParser.CtxExtContext context)
            => throw new NotSupportedException();

        public SyntaxNode VisitDef([NotNull] QtParser.DefContext context)
        {
            string name = context.name.Text;
            List<CtxExt> ctxExts = ParseCtxExts(context._exts);
            Expr retTy = (Expr)context.retTy.Accept(this);
            Expr retExpr = (Expr)context.body.Accept(this);
            return new Def(name, ctxExts, retTy, retExpr);
        }

        public SyntaxNode VisitErrorNode(IErrorNode node)
            => throw new NotSupportedException();

        public SyntaxNode VisitElimExpr([NotNull] QtParser.ElimExprContext context)
        {
            Expr discriminee = (Expr)context.discriminee.Accept(this);
            List<CtxExt> intoExts = ParseCtxExts(context._exts);
            Expr intoTy = (Expr)context.intoTy.Accept(this);
            List<ElimCase> cases = context._cases.Select(ec => (ElimCase)ec.Accept(this)).ToList();
            return new ElimExpr(discriminee, intoExts, intoTy, cases);
        }

        public SyntaxNode VisitElimCase([NotNull] QtParser.ElimCaseContext context)
        {
            List<CtxExt> caseExts = ParseCtxExts(context._exts);
            Expr caseTy = (Expr)context.caseTy.Accept(this);
            Expr body = (Expr)context.body.Accept(this);
            return new ElimCase(caseExts, caseTy, body);
        }

        public SyntaxNode VisitExpr([NotNull] QtParser.ExprContext context)
        {
            if (context.parenthesized != null)
                return context.parenthesized.Accept(this);
            if (context.let != null)
                return context.let.Accept(this);
            if (context.id != null)
                return context.id.Accept(this);
            if (context.elim != null)
                return context.elim.Accept(this);

            Debug.Assert(context.fun != null && context._args.Count > 0);
            return new AppExpr(context.fun.Text, context._args.Select(a => (Expr)a.Accept(this)).ToList());
        }

        public SyntaxNode VisitIdExpr([NotNull] QtParser.IdExprContext context)
        {
            return new IdExpr(context.id.Text);
        }

        public SyntaxNode VisitLetExpr([NotNull] QtParser.LetExprContext context)
        {
            string name = context.varName.Text;
            Expr type = (Expr)context.ty.Accept(this);
            Expr val = (Expr)context.val.Accept(this);
            Expr body = (Expr)context.body.Accept(this);
            return new LetExpr(name, type, val, body);
        }

        public SyntaxNode VisitTerminal(ITerminalNode node)
            => throw new NotSupportedException();

        public SyntaxNode VisitUnit([NotNull] QtParser.UnitContext context)
        {
            return new Unit(context._defs.Select(d => (Def)d.Accept(this)).ToList());
        }
    }
}
