﻿using Antlr4.Runtime;
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
def zero (a b c d e : nat) (_ : a = b) (_ : b = c) (lucky : c = d) (_ : d = e) : e = a := lucky.

def negb (b : bool) : bool :=
  elim b into (_ : bool) : bool
  | => false
  | => true.

def plus (a b : nat) : nat :=
  elim a into (_ : nat) : nat
  | => b
  | (_ : nat) (prev : nat) => S prev.

def plus_0_r (a : nat) : a + 0 = a :=
  elim a into (n : nat) : n + 0 = n
  | => plus_0_l 0
  | (pred : nat) (IH : pred + 0 = pred) =>
    let _ : S pred + 0 = S (pred + 0) := plus_Sn_m pred 0 in
    refl (S pred).
";

            Unit unit = AstParser.ParseUnit(Example);
            Console.WriteLine(unit);
            using (var tc = new TypeChecker())
            {
                tc.TypeCheck(unit.Definitions[0]);
            }
        }
    }
}
