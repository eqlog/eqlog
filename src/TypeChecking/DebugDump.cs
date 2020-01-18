using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Text;

namespace QT.TypeChecking
{
    internal static class DebugDump
    {
        public static StringBuilder CreateTest(IEnumerable<CwfNode> nodes)
        {
            StringBuilder sb = new StringBuilder();
            sb.AppendLine("[Fact]");
            sb.AppendLine("public void Test()");
            sb.AppendLine("{");
            sb.AppendLine("using Z3Model m = new Z3Model();");

            foreach (CwfNode node in nodes.OrderBy(n => n.Id))
            {
                MethodInfo gen = typeof(Z3Model).GetMethods().Single(m => m.ReturnType == node.GetType());
                sb.AppendFormat("{0} n{1} = m.{2}(", node.GetType().Name, node.Id, gen.Name);
                void Args(params CwfNode[] nodes) => sb.AppendJoin(", ", nodes.Select(n => $"n{n.Id}"));

                switch (node)
                {
                    case EmptyCtx ctx: Args(); break;
                    case ComprehensionCtx ctx: Args(ctx.BaseCtx, ctx.CompTy); break;
                    case ProjMorph morph: Args(morph.Domain); break;
                    case ProjTm tm: Args(tm.Ctx); break;
                    case IdMorph morph: Args(morph.Domain); break;
                    case CompMorph morph: Args(morph.G, morph.F); break;
                    case ExtensionMorph morph: Args(morph.Morph, morph.Tm, morph.Codomain.CompTy); break;
                    case SubstTy ty: Args(ty.BaseTy, ty.Morph); break;
                    case SubstTm tm: Args(tm.BaseTm, tm.Morph); break;
                    case IdTy ty: Args(ty.Left, ty.Right); break;
                    case ReflTm tm: Args(tm.EqTm); break;
                    case BoolTy ty: Args(ty.Ctx); break;
                    case TrueTm tm: Args(tm.Ctx); break;
                    case FalseTm tm: Args(tm.Ctx); break;
                    case ElimBoolTm tm: Args(tm.Ty, tm.TrueCase, tm.FalseCase); break;
                    default: throw new Exception("Unreachable");
                }

                sb.AppendLine(");");
            }

            sb.AppendLine("m.Verify();");
            sb.Append("}");
            return sb;
        }
    }
}
