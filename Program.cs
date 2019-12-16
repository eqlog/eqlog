using Antlr4.Runtime;
using Microsoft.Z3;
using QT.Parse;
using System;
using System.Collections.Generic;
using System.Text;

namespace QT
{
    internal static class Program
    {
        private static void Main(string[] args)
        {
            Console.OutputEncoding = Encoding.UTF8;

            const string Example = @"
def negb (b : bool) : bool :=
  elim b into (x : bool) : bool
  | : bool => false
  | : bool => true.

def plus_0_r (a : nat) : Id (plus a O) a :=
  elim a into (n : nat) : Id (plus n O) n
  | : Id (plus O O) O => plus_0_l O
  | (pred : nat)
    (IH : Id (plus pred O) pred) : Id (plus (S pred) O) (S pred) =>
    let _ : Id (plus (S pred) O) (S (plus pred O)) :=
      plus_Sn_m pred O in
    refl (S pred).
";

            Unit unit = AstParser.ParseUnit(Example);
            Console.WriteLine(unit);
            Console.ReadLine();
            using (var tc = new TypeChecker())
            {
                Console.WriteLine(tc.Check(unit, out string err) ? "Type checking succeeded" : ("Type checking error: " + err));
            }
        }
    }
}
