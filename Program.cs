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

//            const string Example = @"
//def negb (b : bool) : bool :=
//  elim b as b into (x : bool) : bool
//  | : bool => false
//  | : bool => true";
            const string Example = @"
def plus_0_r (a : nat) : Id (plus a _0) a :=
  elim a as n into (n : nat) : Id (plus n _0) n
  | : Id (plus _0 _0) _0 => plus_0_l _0
  | (pred : nat)
    (IH : Id (plus pred _0) pred) : Id (plus (S pred) _0) (S (plus pred _0)) =>
    let _ : Id (plus (S pred) _0) (S (plus pred _0)) := plus_Sn_m pred _0 in
    refl (S pred)
";

//            const string Example = @"
//def plus_0_r (a : nat) : a + 0 = a :=
//  match a return (n : nat) -> n + 0 = n with
//  | 0 => plus_0_l 0
//  | S n, (prev : n + 0 = n) =>
//    let _ : S n + 0 = S (n + 0) := plus_Sn_m n 0 in
//    refl n
//  end


//def plus_comm (a b : nat) : plus a b = plus b a :=
//  c1 : 0 + b = b := plus_0_l b
//  c2 : b + 0 = b := add_0_r b
//  match a return (n : nat) -> n + b = b + n with
//  | 0 => refl b
//  | S n, (prev :  => 
  

//def negb_example (x : bool) (negb false = x) :=
  
//";

            Unit unit = AstParser.ParseUnit(Example);
            Console.WriteLine(unit);
            Console.ReadLine();
            //using (var tc = new TypeChecker())
            //{
            //    Console.WriteLine();
            //}
        }
    }
}
