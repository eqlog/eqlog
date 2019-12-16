﻿using Antlr4.Runtime;
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
  elim b into (_ : bool) : bool
  | : bool => false
  | : bool => true.

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
            Console.ReadLine();
            using (var tc = new TypeChecker())
            {
                Console.WriteLine(tc.Check(unit, out string err) ? "Type checking succeeded" : ("Type checking error: " + err));
            }
        }
    }
}
