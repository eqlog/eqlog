using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace QT
{
    internal static class PrettyPrinter
    {
        public static void Print(SyntaxNode node, StringBuilder sb)
        {
            switch (node)
            {
                case Unit unit:
                    for (int i = 0; i < unit.Definitions.Count; i++)
                    {
                        if (i > 0)
                            sb.AppendLine().AppendLine();

                        Print(unit.Definitions[i], sb);
                    }
                    break;
                case Def def:
                    int defIndex = LineLength(sb);
                    sb.AppendFormat("def {0} ", def.Name);
                    PrintCtxExts(def.CtxExts, def.RetTy, sb);
                    sb.Append(" :=").AppendLine().Append(' ', defIndex + 2);
                    Print(def.Body, sb);
                    sb.Append('.');
                    break;
                case DefId defId:
                    sb.Append(defId.Name);
                    break;
                case CtxExt ctxExt:
                    sb.AppendFormat("{0} : ", ctxExt.Name);
                    Print(ctxExt.Type, sb);
                    break;
                case LetExpr let:
                    int letIndex = LineLength(sb);
                    int letLineStart = sb.Length - letIndex;
                    sb.AppendFormat("let {0} : ", let.Name);
                    Print(let.Type, sb);
                    sb.Append(" := ");
                    int letValStart = sb.Length;
                    Print(let.Val, sb);
                    if (sb.Length - letLineStart > 80)
                    {
                        sb.Remove(letValStart, sb.Length - letValStart);
                        sb.Remove(sb.Length - 1, 1);
                        sb.AppendLine().Append(' ', letIndex + 2);
                        Print(let.Val, sb);
                    }
                    sb.Append(" in").AppendLine();
                    sb.Append(' ', letIndex);
                    Print(let.Body, sb);
                    break;
                case IdExpr id:
                    sb.Append(id.Id);
                    break;
                case ElimExpr elim:
                    int elimIndex = LineLength(sb);
                    sb.Append("elim ");
                    Print(elim.Discriminee, sb);
                    sb.Append(" into ");
                    PrintCtxExts(elim.IntoExts, elim.IntoTy, sb);
                    foreach (ElimCase @case in elim.Cases)
                    {
                        sb.AppendLine();
                        sb.Append(' ', elimIndex);
                        Print(@case, sb);
                    }
                    break;
                case ElimCase @case:
                    sb.Append("| ");
                    int caseIndex = LineLength(sb);
                    PrintCtxExts(@case.CaseExts, null, sb);
                    sb.Append(" => ");
                    int startOfArrowLine = sb.Length - LineLength(sb);
                    int startOfBody = sb.Length;
                    Print(@case.Body, sb);
                    if (sb.Length - startOfArrowLine > 80)
                    {
                        sb.Remove(startOfBody, sb.Length - startOfBody);
                        sb.Remove(sb.Length - 1, 1);
                        sb.AppendLine();
                        sb.Append(' ', caseIndex);
                        Print(@case.Body, sb);
                    }
                    break;
                case AppExpr app:
                    sb.Append(app.Fun);
                    sb.Append(" ");
                    void PrintArg(Expr e)
                    {
                        bool parenthesize = !(e is IdExpr);
                        sb.Append(parenthesize ? "(" : "");
                        Print(e, sb);
                        sb.Append(parenthesize ? ")" : "");
                    }

                    int argIndent = LineLength(sb);
                    int startOfAppLine = sb.Length - argIndent;
                    PrintArg(app.Args[0]);

                    int startOfSecondArg = sb.Length;

                    foreach (Expr arg in app.Args.Skip(1))
                    {
                        sb.Append(" ");
                        PrintArg(arg);
                    }

                    if (sb.Length - startOfAppLine > 80 && app.Args.Count > 1)
                    {
                        sb.Remove(startOfSecondArg, sb.Length - startOfSecondArg);
                        foreach (Expr arg in app.Args.Skip(1))
                        {
                            sb.AppendLine();
                            sb.Append(' ', argIndent);
                            PrintArg(arg);
                        }
                    }

                    break;
                default:
                    throw new ArgumentException("Cannot handle " + node.GetType().Name, nameof(node));
            }
        }

        private static int LineLength(StringBuilder sb)
        {
            if (sb.Length < Environment.NewLine.Length)
                return sb.Length;

            int index = sb.Length - Environment.NewLine.Length;
            while (index >= 0 && sb.ToString(index, Environment.NewLine.Length) != Environment.NewLine)
                index--;

            if (index == -1)
                return sb.Length;

            return sb.Length - (index + Environment.NewLine.Length);
        }

        private static void PrintCtxExts(
            IEnumerable<CtxExt> exts, Expr? tyAnnot, StringBuilder sb)
        {
            int start = sb.Length;
            bool first = true;
            foreach (CtxExt ext in exts)
            {
                if (!first)
                    sb.Append(' ');

                sb.Append("(");
                Print(ext, sb);
                sb.Append(")");

                first = false;
            }

            int colonLineStart = sb.Length - LineLength(sb);
            if (tyAnnot != null)
            {
                if (!first)
                    sb.Append(' ');

                sb.Append(": ");
                Print(tyAnnot, sb);
            }

            if (sb.Length - colonLineStart <= 80)
                return;

            sb.Remove(start, sb.Length - start);
            int startIndex = LineLength(sb);
            first = true;
            foreach (CtxExt ext in exts)
            {
                if (!first)
                {
                    sb.AppendLine();
                    sb.Append(' ', startIndex);
                }

                sb.Append('(');
                Print(ext, sb);
                sb.Append(')');
                first = false;
            }

            if (tyAnnot != null)
            {
                if (!first)
                    sb.Append(' ');

                sb.Append(": ");
                Print(tyAnnot, sb);
            }
        }
    }
}
