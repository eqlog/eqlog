#![recursion_limit = "128"]
extern crate indoc;
extern crate lalrpop_util;
#[cfg(test)]
extern crate maplit;
use lalrpop_util::lalrpop_mod;

lalrpop_mod!(
    #[allow(unused)]
    grammar
);
pub mod ast;

pub mod cwf_checker;

#[cfg(test)]
mod tests {

    use crate::cwf_checker::*;
    use crate::grammar::UnitParser;
    use indoc::indoc;

    fn check(source: &str) {
        let defs = UnitParser::new().parse(source).unwrap();

        let mut scope = Scope::new();
        for def in defs.iter() {
            scope.add_definition(Checking::Yes, def);
        }
    }

    #[test]
    fn test_unit_identity() {
        let src = indoc! {"
            def id(x: Unit) : Unit := x.
        "};
        check(&src);
    }

    #[test]
    fn test_unit_nested_identity() {
        let src = indoc! {"
            def id (x: Unit) : Unit :=
              let
                def id0 (y: Unit) : Unit := y.
              in
                id0(x).
        "};
        check(&src);
    }

    #[test]
    fn test_unit_term() {
        let src = indoc! {"
            def u : Unit := unit.
        "};
        check(&src);
    }

    #[test]
    fn test_let_unit_term() {
        let src = indoc! {"
            def u : Unit :=
              let
                def x : Unit := unit.
                def y : Unit := x.
              in y.
        "};
        check(&src);
    }

    #[test]
    fn test_unit_unit_refl() {
        let src = indoc! {"
            def r : unit = unit := refl unit.
        "};
        check(&src);
    }

    #[test]
    #[should_panic]
    fn test_unit_equaity_not_well_typed() {
        let src = indoc! {"
            def r : unit = unit := unit.
        "};
        check(&src);
    }

    #[test]
    fn test_app_unit_identity() {
        let src = indoc! {"
            def id (x: Unit) : Unit := x.
            def r : unit = id(unit) := refl unit.
        "};
        check(&src);
    }

    #[test]
    fn test_app_unit_nested_identity() {
        let src = indoc! {"
            def id (x: Unit) : Unit :=
              let
                def id0 (y: Unit) : Unit := y.
              in
                id0(x).
            dump 'id defined'.
            def r : unit = id(unit) := refl unit.
            dump 'done'.
        "};
        check(&src);
    }

    #[test]
    #[should_panic]
    fn test_app_unit_iterated_identity_not_expanded() {
        let src = indoc! {"
            def id0 (x0: Unit) : Unit := x0.
            dump 'id0 defined'.
            def id1 (x1: Unit) : Unit := id0(x1).
            dump 'id1 defined'.
            def r : unit = id1(unit) := refl unit.
            dump 'done'.
        "};
        check(&src);
    }

    #[test]
    fn test_app_unit_iterated_identity_expanded() {
        let src = indoc! {"
            def id0 (x0: Unit) : Unit := x0.
            dump 'id0 defined'.
            def id1 (x1: Unit) : Unit := id0(x1).
            dump 'id1 defined'.
            def r : id0(unit) = id1(unit) := refl unit.
            dump 'done'.
        "};
        check(&src);
    }

    #[test]
    fn test_app_refl() {
        let src = indoc! {"
            def r (x : Unit) : x = x := refl x.
            def s : unit = unit := r(unit).
        "};
        check(&src);
    }

    #[test]
    fn test_unit_uniqueness() {
        let src = indoc! {"
            def unique_based (x : Unit) : x = unit :=
              elim_unit x into (x0 : Unit) : x0 = unit
                | unit => (refl unit : unit = unit)
              .
        "};
        check(&src);
    }

    #[test]
    fn test_app_unit_uniqueness() {
        let src = indoc! {"
            def unique_based (x : Unit) : x = unit :=
              elim_unit x into (x0 : Unit) : x0 = unit
                | unit => (refl unit : unit = unit)
              .
            def unique (x : Unit) (y : Unit) : x = y :=
              let
                def xu : x = unit := unique_based(x).
                def yu : y = unit := unique_based(y).
              in
                refl unit
              .
        "};
        check(&src);
    }

    #[test]
    fn test_app_const_unit() {
        let src = indoc! {"
            def const_unit (x : Unit) : Unit :=
              elim_unit x into (x0 : Unit) : Unit
                | unit => unit
              .
            def u : Unit := const_unit(unit).
            def r : u = unit := refl unit.
        "};
        check(&src);
    }

    #[test]
    fn test_first_bool() {
        let src = indoc! {"
            def first (x: Bool) (y: Bool) : Bool := x.
            def r : first(false, true) = false := refl false.
        "};
        check(&src);
    }

    #[test]
    #[should_panic]
    fn test_bad_first_bool() {
        let src = indoc! {"
            def first (x: Bool) (y: Bool) : Bool := x.
            dump 'first defined'.
            def r : first(false, true) = true := refl true.
        "};
        check(&src);
    }

    #[test]
    fn test_bool_not() {
        let src = indoc! {"
            def not (x : Bool) : Bool :=
              elim_bool x into (x0 : Bool) : Bool
                | false => true
                | true => false
              .
            def r0 : not(true) = false := refl false.
            def r1 : not(false) = true := refl true.
        "};
        check(&src);
    }

    #[test]
    fn test_bool_and_def() {
        let src = indoc! {"
            def and (x : Bool) (y : Bool) : Bool :=
              elim_bool x into (x1 : Bool) : Bool
                | false => false
                | true => y
              .
            dump 'and defined'.

            def false_false : and(false, false) = false := refl false.
            def true_false : and(true, false) = false := refl false.
            def false_true : and(false, true) = false := refl false.
            def true_true : and(true, true) = true := refl true.
        "};
        check(&src);
    }

    #[test]
    fn test_bool_fixed_false_and() {
        let src = indoc! {"
            def and (x : Bool) (y : Bool) : Bool :=
              elim_bool x into (x1 : Bool) : Bool
                | false => false
                | true => y
              .

            def first_false (y: Bool) : and(false, y) = false := refl false.
            def second_false (x: Bool) : and(x, false) = false :=
              elim_bool x into (x0 : Bool) : and(x0, false) = false
                | false => (refl false : and(false, false) = false)
                | true => (refl false : and(true, false) = false)
              .

            dump 'done'.
        "};
        check(&src);
    }

    #[test]
    fn test_bool_fixed_true_and() {
        let src = indoc! {"
            def and (x : Bool) (y : Bool) : Bool :=
              elim_bool x into (x1 : Bool) : Bool
                | false => false
                | true => y
              .

            def first_true (y: Bool) : and(true, y) = y := refl y.
            def second_true (x: Bool) : and(x, true) = x :=
              elim_bool x into (x0 : Bool) : and(x0, true) = x0
                | false => (refl false : and(false, true) = false)
                | true => (refl true : and(true, true) = true)
              .

            dump 'done'.
        "};
        check(&src);
    }

    #[test]
    fn test_bool_and_commutative() {
        let src = indoc! {"
            def and (x : Bool) (y : Bool) : Bool :=
              elim_bool x into (x1 : Bool) : Bool
                | false => false
                | true => y
              .

            def first_false (y: Bool) : and(false, y) = false := refl false.
            def second_false (x: Bool) : and(x, false) = false :=
              elim_bool x into (x0 : Bool) : and(x0, false) = false
                | false => (refl false : and(false, false) = false)
                | true => (refl false : and(true, false) = false)
              .

            def first_true (y: Bool) : and(true, y) = y := refl y.
            def second_true (x: Bool) : and(x, true) = x :=
              elim_bool x into (x0 : Bool) : and(x0, true) = x0
                | false => (refl false : and(false, true) = false)
                | true => (refl true : and(true, true) = true)
              .

            def and_commutative (x : Bool) (y : Bool) : and(x, y) = and(y, x) :=
              elim_bool x into (x0 : Bool) : and(x0, y) = and(y, x0)
                | false =>
                    let
                      def left_is_false : and(false, y) = false := first_false(y).
                      def right_is_false : and(y, false) = false := second_false(y).
                    in
                      refl false
                | true =>
                    let
                      def left_is_y : and(true, y) = y := first_true(y).
                      def right_is_y : and(y, true) = y := second_true(y).
                    in
                      refl y
              .
        "};
        check(&src);
    }

    #[test]
    fn test_bool_and_substitution() {
        let src = indoc! {"
            def and0 (x0 : Bool) (y0 : Bool) : Bool :=
              elim_bool x0 into (_ : Bool) : Bool
                | false => false
                | true => y0
                .

            def and1 (x1 : Bool) (y1 : Bool) : Bool :=
              let
                def result : Bool :=
                  elim_bool x1 into (_ : Bool) : Bool
                    | false => false
                    | true => y1
                    .
                def eq : result = and0(x1, y1) := refl result.
              in
                result
              .
        "};
        check(&src);
    }

    #[test]
    fn test_unit_substitution() {
        let src = indoc! {"
            def unit0 (x0 : Unit) : Unit :=
              elim_unit x0 into (_0 : Unit) : Unit
                | unit => unit
                .

            def unit1 (x1 : Unit) : Unit :=
              let
                def result : Unit :=
                  elim_unit x1 into (_1 : Unit) : Unit
                    | unit => unit
                    .
                def eq : result = unit0(x1) := refl result.
              in
                result
              .
        "};
        check(&src);
    }

    #[test]
    fn test_zero_succ() {
        let src = indoc! {"
            def nat0 : Nat := zero.
            def nat1 : Nat := succ nat0.
            def nat2 : Nat := succ nat1.
        "};
        check(&src);
    }
}
