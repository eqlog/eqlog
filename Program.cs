using System;
using System.Collections.Generic;

namespace QT
{
    internal abstract class SyntaxNode
    {
    }

    internal class Star : SyntaxNode
    {
        public override string ToString() => "*";
    }

    internal class Pi : SyntaxNode
    {
        public Pi(SyntaxNode ty, SyntaxNode body)
        {
            Ty = ty;
            Body = body;
        }

        public SyntaxNode Ty { get; }
        public SyntaxNode Body { get; }

        public override string ToString() => $"(Π{Ty}.{Body})";
    }

    internal class Var : SyntaxNode
    {
        public Var(int index) => Index = index;
        public int Index { get; }

        public override string ToString() => Index.ToString();
    }

    internal class App : SyntaxNode
    {
        public App(SyntaxNode fun, SyntaxNode arg)
        {
            Fun = fun;
            Arg = arg;
        }

        public SyntaxNode Fun { get; }
        public SyntaxNode Arg { get; }

        public override string ToString() => $"{Fun} {Arg}";
    }

    internal class Abs : SyntaxNode
    {
        public Abs(SyntaxNode ty, SyntaxNode body)
        {
            Ty = ty;
            Body = body;
        }

        public SyntaxNode Ty { get; }
        public SyntaxNode Body { get; }

        public override string ToString() => $"(λ{Ty}.{Body})";
    }

    internal class Id : SyntaxNode
    {
        public Id(SyntaxNode left, SyntaxNode right)
        {
            Left = left;
            Right = right;
        }

        public SyntaxNode Left { get; }
        public SyntaxNode Right { get; }
        
        public override string ToString() => $"Id {Left} {Right}";
    }

    internal class Refl : SyntaxNode
    {
        public Refl(SyntaxNode body) => Body = body;
        public SyntaxNode Body { get; }

        public override string ToString() => $"Refl {Body}";
    }

    internal static class Program
    {
        private static void Main(string[] args)
        {
            // fun (T : *) (x : T) => x
            var polyId =
                new Abs(
                    new Star(),
                    new Abs(
                        new Var(0),
                        new Var(0)));
            Console.WriteLine(PrettyPrint(polyId));
            // fun (T : *) (x y : T) (eq : x = y) => (refl x : y = x)
            var refl =
                new Abs(
                    new Star(),
                    new Abs(
                        new Var(0),
                        new Abs(
                            new Var(1),
                            new Abs(
                                new Id(new Var(1), new Var(0)),
                                new Refl(new Id(new Var(2)))))));
            Console.WriteLine(PrettyPrint(refl));
        }

        private static string PrettyPrint(SyntaxNode node)
        {
            List<string> names = new List<string>();
            const string pool = "abcdefghijklmnopqrstuvwxyz";
            string NextName()
            {
                string name =
                    names.Count >= pool.Length
                    ? $"v{names.Count}" : $"{pool[names.Count]}";
                names.Add(name);
                return name;
            }

            string GetName(int var) => names[names.Count - 1 - var];

            string Aux(SyntaxNode sn)
            {
                switch (sn)
                {
                    case Star { }: return "*";
                    case Pi { Ty: var t, Body: var b }:
                        string piTyS = Aux(t);
                        string piIndexN = NextName();
                        string piBodyS = Aux(b);
                        return $"(Π({piIndexN} : {piTyS}).{piBodyS})";
                    case Var { Index: var i }: return GetName(i);
                    case App { Fun: var f, Arg: var a }: return $"{Aux(f)} {Aux(a)}";
                    case Abs { Ty: var t, Body: var b }:
                        string absTyS = Aux(t);
                        string absIndexN = NextName();
                        string absBodyS = Aux(b);
                        return $"(λ({absIndexN} : {absTyS}).{absBodyS})";
                    case Id { Left: var l, Right: var r }: return $"({Aux(l)} = {Aux(r)})";
                    case Refl { Id: { Left: var l, Right: var r } }: return $"(Refl {Aux(l)} {Aux(r)})";
                    default: throw new Exception("Unreachable");
                }
            };

            return Aux(node);
        }
    }
}
