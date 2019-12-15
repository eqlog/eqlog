using Antlr4.Runtime;
using System;
using System.IO;
using System.Text;

namespace QT.Parse
{
    internal static class AstParser
    {
        public static Unit ParseUnit(string body)
        {
            StringBuilder lexerOutput = new StringBuilder();
            StringBuilder lexerErrOutput = new StringBuilder();
            QtLexer lexer = new QtLexer(new AntlrInputStream(body), new StringWriter(lexerOutput), new StringWriter(lexerErrOutput));
            StringBuilder parserOutput = new StringBuilder();
            StringBuilder parserErrOutput = new StringBuilder();
            QtParser parser = new QtParser(new CommonTokenStream(lexer), new StringWriter(parserOutput), new StringWriter(parserErrOutput));
            QtParser.UnitContext unit = parser.unit();
            if (lexerErrOutput.Length > 0)
                throw new ArgumentException(lexerErrOutput.ToString(), "body");
            if (parserErrOutput.Length > 0)
                throw new ArgumentException(parserErrOutput.ToString(), "body");
            return (Unit)unit.Accept(new ToAstVisitor());
        }
    }
}
