using Antlr4.Runtime.Misc;
using Antlr4.Runtime.Tree;
using QT;
using System;
using System.Collections.Generic;
using System.Linq;

namespace QT.Parse
{
    internal class ToAstVisitor : IQtVisitor<SyntaxNode>
    {
        public SyntaxNode Visit(IParseTree tree)
            => throw new NotSupportedException();

        public SyntaxNode VisitChildren(IRuleNode node)
            => throw new NotSupportedException();

        public SyntaxNode VisitDef([NotNull] QtParser.DefContext context)
        {
            string name = context.name.Text;
            List<Param> @params = context.param().SelectMany(p => p.ID().Select(id => new Param(id.GetText(), (Ty)p.ty().Accept(this)))).ToList();
            Ty retTy = (Ty)context.retTy.Accept(this);
            Expr retExpr = (Expr)context.body.Accept(this);
            return new Def(name, @params, retTy, retExpr);
        }

        public SyntaxNode VisitErrorNode(IErrorNode node)
            => throw new NotSupportedException();

        public SyntaxNode VisitExpr([NotNull] QtParser.ExprContext context)
        {
            return context.letExpr() == null ? context.idExpr().Accept(this) : context.letExpr().Accept(this);
        }

        public SyntaxNode VisitIdExpr([NotNull] QtParser.IdExprContext context)
        {
            return new IdExpr(context.ID().GetText());
        }

        public SyntaxNode VisitLetExpr([NotNull] QtParser.LetExprContext context)
        {
            string id = context.varName.Text;
            Ty type = (Ty)context.ty().Accept(this);
            Expr val = (Expr)context.val.Accept(this);
            Expr body = (Expr)context.body.Accept(this);
            return new LetExpr(id, type, val, body);
        }

        public SyntaxNode VisitParam([NotNull] QtParser.ParamContext context)
            => throw new NotSupportedException();

        public SyntaxNode VisitTerminal(ITerminalNode node)
            => throw new NotSupportedException();

        public SyntaxNode VisitTy([NotNull] QtParser.TyContext context)
            => new Ty(context.ID().GetText());

        public SyntaxNode VisitUnit([NotNull] QtParser.UnitContext context)
        {
            return new Unit(context.def().Select(d => (Def)d.Accept(this)).ToList());
        }
    }
}
