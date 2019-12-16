using Antlr4.Runtime.Misc;
using Antlr4.Runtime.Tree;
using QT;
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

        public SyntaxNode VisitChildren(IRuleNode node)
            => throw new NotSupportedException();

        private List<CtxExt> ParseCtxExts(IEnumerable<QtParser.CtxExtContext> ctxs)
        {
            IEnumerable<CtxExt> MakeExts(QtParser.CtxExtContext ctx)
            {
                Expr ty = (Expr)ctx.ty.Accept(this);
                return ctx.ID().Select(id => new CtxExt(id.GetText(), ty));
            }
            List<CtxExt> l = ctxs.SelectMany(MakeExts).ToList();
            return l;
        }

        public SyntaxNode VisitCtxExt([NotNull] QtParser.CtxExtContext context)
            => throw new NotSupportedException();

        public SyntaxNode VisitDef([NotNull] QtParser.DefContext context)
        {
            string name = context.name.Text;
            List<CtxExt> ctxExts = ParseCtxExts(context.ctxExt());
            Expr retTy = (Expr)context.retTy.Accept(this);
            Expr retExpr = (Expr)context.body.Accept(this);
            return new Def(name, ctxExts, retTy, retExpr);
        }

        public SyntaxNode VisitErrorNode(IErrorNode node)
            => throw new NotSupportedException();

        public SyntaxNode VisitElimExpr([NotNull] QtParser.ElimExprContext context)
        {
            Expr discriminee = (Expr)context.discriminee.Accept(this);
            string varName = context.varName.Text;
            List<CtxExt> intoExts = ParseCtxExts(context.ctxExt());
            Expr intoTy = (Expr)context.intoTy.Accept(this);
            List<ElimCase> cases = context.elimCase().Select(ec => (ElimCase)ec.Accept(this)).ToList();

            return new ElimExpr(discriminee, varName, intoExts, intoTy, cases);
        }

        public SyntaxNode VisitElimCase([NotNull] QtParser.ElimCaseContext context)
        {
            List<CtxExt> caseExts = ParseCtxExts(context.ctxExt());
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

            Debug.Assert(context.fun != null && context.arg != null);
            return new AppExpr((Expr)context.fun.Accept(this), (Expr)context.arg.Accept(this));
        }

        public SyntaxNode VisitIdExpr([NotNull] QtParser.IdExprContext context)
        {
            return new IdExpr(context.ID().GetText());
        }

        public SyntaxNode VisitLetExpr([NotNull] QtParser.LetExprContext context)
        {
            string id = context.varName.Text;
            Expr type = (Expr)context.ty.Accept(this);
            Expr val = (Expr)context.val.Accept(this);
            Expr body = (Expr)context.body.Accept(this);
            return new LetExpr(id, type, val, body);
        }

        public SyntaxNode VisitTerminal(ITerminalNode node)
            => throw new NotSupportedException();

        public SyntaxNode VisitUnit([NotNull] QtParser.UnitContext context)
        {
            return new Unit(context.def().Select(d => (Def)d.Accept(this)).ToList());
        }
    }
}
