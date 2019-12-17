using Antlr4.Runtime;
using System;
using System.IO;
using System.Text;

namespace QT.Parse
{
    internal static class AstParser
    {
        private static readonly ToAstVisitor s_toAst = new ToAstVisitor();
        public static Expr ParseExpr(string body)
            => (Expr)ParseT(body, parser => parser.expr()).Accept(s_toAst);

        public static Unit ParseUnit(string body)
            => (Unit)ParseT(body, parser => parser.unit()).Accept(s_toAst);

        private static T ParseT<T>(string body, Func<QtParser, T> fun)
        {
            StringBuilder lexerOutput = new StringBuilder();
            StringBuilder lexerErrOutput = new StringBuilder();
            QtLexer lexer = new QtLexer(new AntlrInputStream(body), new StringWriter(lexerOutput), new StringWriter(lexerErrOutput));
            StringBuilder parserOutput = new StringBuilder();
            StringBuilder parserErrOutput = new StringBuilder();
            QtParser parser = new QtParser(new CommonTokenStream(lexer), new StringWriter(parserOutput), new StringWriter(parserErrOutput));
            T result = fun(parser);
            if (lexerErrOutput.Length > 0)
                throw new ArgumentException(lexerErrOutput.ToString(), "body");
            if (parserErrOutput.Length > 0)
                throw new ArgumentException(parserErrOutput.ToString(), "body");
            return result;
        }
    }
}
