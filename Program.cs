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

            string Example = @"
def test (a : nat) :
a = elim a into (_ : nat) : nat
    | => 0
    | (pred : nat) (_ : nat) => S pred :=
  elim a into (n : nat) : (n = elim n into (_ : nat) : nat
                           | => 0
                           | (pred : nat) (_ : nat) => S pred)
  | => refl 0
  | (pred : nat)
    (_ : pred = elim pred into (_ : nat) : nat
                | => 0
                | (pred : nat) (_ : nat) => S pred) => refl (S pred).

  (*let test : nat :=
  elim a into (_ : nat) : nat
  | => 0
  | (_ : nat) (prev : nat) => S prev in
  let _ : test = 1 := dump ElimNat (dump TmEq (refl test)) in
  0.*)
  
(*
def plus (a b : nat) : nat :=

def plus_0_l (a : nat) : 0 + a = a :=
  refl a.

def plus_2_2 : 2 + 2 = 4 :=
  let _ : 1 + 3 = 2 + 2 := plus_Sn_m 2 2 in
  let _ : 0 + 4 = 1 + 3 := plus_Sn_m 1 3 in
  refl 4.

def plus_0_r (a : nat) : a + 0 = a :=
  elim a into (n : nat) : n + 0 = n
  | => plus_0_l 0
  | (pred : nat)
    (IH : pred + 0 = pred) =>
    let _ : S pred + 0 = S (pred + 0) := plus_Sn_m pred 0 in
    refl (S pred).

def zero (a b c d e f : nat)
         (_ : a = b)
         (_ : b = c)
         (_ : c = d)
         (_ : d = e)
         (_ : e = f) : a = f :=
  dump TmEq (refl a).

def UIP (a b : nat) (p q : a = b) : p = q :=
  
*)
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
