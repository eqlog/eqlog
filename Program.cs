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
def zero (n : nat) (p : n = 0) : 0 = n := p.

def negb (b : bool) : bool :=
  elim b into (_ : bool) : bool
  | : bool => false
  | : bool => true.

def plus (a b : nat) : nat :=
  elim a into (_ : nat) : nat
  | : nat => b
  | (_ : nat) (prev : nat) : nat => S prev.

def plus_0_r (a : nat) : a + 0 = a :=
  elim a into (n : nat) : n + 0 = n
  | : 0 + 0 = 0 => plus_0_l 0
  | (pred : nat)
    (IH : pred + 0 = pred) : S pred + 0 = S pred =>
    let _ : S pred + 0 = S (pred + 0) := plus_Sn_m pred 0 in
    refl (S pred).
";

            Unit unit = AstParser.ParseUnit(Example);
            Console.WriteLine(unit);
            using (var tc = new TypeChecker())
            {
                foreach (Def d in unit.Definitions)
                    tc.TypeCheck(d);
            }
        }
    }
}
