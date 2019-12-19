using Antlr4.Runtime;
using Microsoft.Z3;
using QT.Parse;
using System;
using System.Collections.Generic;
using System.Text;

[assembly: CLSCompliant(false)]

namespace QT
{
    internal static class Program
    {
        private static void Main(string[] args)
        {
            Console.OutputEncoding = Encoding.UTF8;

            const string Example = @"
def zero (a b c d : nat)
         (_ : a = b)
         (_ : c = d)
         (_ : b = c) : a = d :=
  dump TyEq (refl a).

def UIP (a b : nat) (p q : a = b) : p = q :=
  dump TmEq (refl p).
";

            Unit unit = AstParser.ParseUnit(Example);
            using (var tc = new TypeChecker())
            {
                foreach (Def def in unit.Definitions)
                {
                    Console.WriteLine(def);
                    tc.TypeCheck(def);
                    Console.WriteLine("OK");
                    Console.WriteLine();
                }
            }
        }
    }
}
