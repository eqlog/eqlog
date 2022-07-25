#![recursion_limit = "128"]
extern crate eqlog_util;
extern crate indoc;
#[cfg(test)]
extern crate maplit;
use eqlog_util::eqlog_mod;
extern crate lalrpop_util;
use lalrpop_util::lalrpop_mod;

lalrpop_mod!(
    #[allow(unused)]
    grammar
);
eqlog_mod!(cwf);
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
            bool_ind not (x : Bool) : Bool
              | false => true
              | true => false
              .
            def r0 : not(true) = false := refl false.
            def r1 : not(false) = true := refl true.
        "};
        check(&src);
    }

    #[test]
    fn test_bool_nested_not() {
        let src = indoc! {"
            def not (x : Bool) : Bool :=
              let 
                bool_ind x_case (x0 : Bool): Bool
                | false => true
                | true => false
                .
              in
                x_case(x)
              .
            def r0 : not(true) = false := refl false.
            def r1 : not(false) = true := refl true.
            dump 'done'.
        "};
        check(&src);
    }

    #[test]
    fn test_bool_and() {
        let src = indoc! {"
            def and (x : Bool) (y : Bool) : Bool :=
              let
                bool_ind x_case (x1 : Bool) : Bool
                  | false => false
                  | true => y
                  .
              in
                x_case(x)
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
              let
                bool_ind x_case (x1 : Bool) : Bool
                  | false => false
                  | true => y
                  .
              in
                x_case(x)
              .

            def and_first_false (y: Bool) : and(false, y) = false := refl false.
            bool_ind and_second_false (x: Bool) : and(x, false) = false
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
              let
                bool_ind x_case (x1 : Bool) : Bool
                  | false => false
                  | true => y
                  .
              in
                x_case(x)
              .

            def and_first_true (y: Bool) : and(true, y) = y := refl y.
            bool_ind and_second_true (x: Bool) : and(x, true) = x
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
              let
                bool_ind x_case (x1 : Bool) : Bool
                  | false => false
                  | true => y
                  .
              in
                x_case(x)
              .

            def first_false (y: Bool) : and(false, y) = false := refl false.
            bool_ind second_false (x: Bool) : and(x, false) = false
              | false => (refl false : and(false, false) = false)
              | true => (refl false : and(true, false) = false)
              .

            def first_true (y: Bool) : and(true, y) = y := refl y.
            bool_ind second_true (x: Bool) : and(x, true) = x
              | false => (refl false : and(false, true) = false)
              | true => (refl true : and(true, true) = true)
              .

            def and_commutative (x : Bool) (y : Bool) : and(x, y) = and(y, x) :=
              let
                bool_ind x_case(x0 : Bool) : and(x0, y) = and(y, x0)
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
              in
                x_case(x)
              .
        "};
        check(&src);
    }

    #[test]
    fn test_twice_bool_and_commutative() {
        let src = indoc! {"
            def and (x : Bool) (y : Bool) : Bool :=
              let
                bool_ind x_case (x1 : Bool) : Bool
                  | false => false
                  | true => y
                  .
              in
                x_case(x)
              .

            def first_false (y: Bool) : and(false, y) = false := refl false.
            bool_ind second_false (x: Bool) : and(x, false) = false
              | false => (refl false : and(false, false) = false)
              | true => (refl false : and(true, false) = false)
              .

            def first_true (y: Bool) : and(true, y) = y := refl y.
            bool_ind second_true (x: Bool) : and(x, true) = x
              | false => (refl false : and(false, true) = false)
              | true => (refl true : and(true, true) = true)
              .

            def and_commutative (x : Bool) (y : Bool) : and(x, y) = and(y, x) :=
              let
                bool_ind x_case(x0 : Bool) : and(x0, y) = and(y, x0)
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
              in
                x_case(x)
              .

            def and1 (x : Bool) (y : Bool) : Bool :=
              let
                bool_ind x_case (x1 : Bool) : Bool
                  | false => false
                  | true => y
                  .
              in
                x_case(x)
              .

            def first_false1 (y: Bool) : and1(false, y) = false := refl false.
            bool_ind second_false1 (x: Bool) : and1(x, false) = false
              | false => (refl false : and1(false, false) = false)
              | true => (refl false : and1(true, false) = false)
              .

            def first_true1 (y: Bool) : and1(true, y) = y := refl y.
            bool_ind second_true1 (x: Bool) : and1(x, true) = x
              | false => (refl false : and1(false, true) = false)
              | true => (refl true : and1(true, true) = true)
              .

            def and_commutative1 (x : Bool) (y : Bool) : and1(x, y) = and1(y, x) :=
              let
                bool_ind x_case(x0 : Bool) : and1(x0, y) = and1(y, x0)
                  | false =>
                      let
                        def left_is_false : and1(false, y) = false := first_false1(y).
                        def right_is_false : and1(y, false) = false := second_false1(y).
                      in
                        refl false
                  | true =>
                      let
                        def left_is_y : and1(true, y) = y := first_true1(y).
                        def right_is_y : and1(y, true) = y := second_true1(y).
                      in
                        refl y
                  .
              in
                x_case(x)
              .
        "};
        check(&src);
    }

    #[test]
    fn test_thrice_bool_and_commutative() {
        let src = indoc! {"
            def and (x : Bool) (y : Bool) : Bool :=
              let
                bool_ind x_case (x1 : Bool) : Bool
                  | false => false
                  | true => y
                  .
              in
                x_case(x)
              .

            def first_false (y: Bool) : and(false, y) = false := refl false.
            bool_ind second_false (x: Bool) : and(x, false) = false
              | false => (refl false : and(false, false) = false)
              | true => (refl false : and(true, false) = false)
              .

            def first_true (y: Bool) : and(true, y) = y := refl y.
            bool_ind second_true (x: Bool) : and(x, true) = x
              | false => (refl false : and(false, true) = false)
              | true => (refl true : and(true, true) = true)
              .

            def and_commutative (x : Bool) (y : Bool) : and(x, y) = and(y, x) :=
              let
                bool_ind x_case(x0 : Bool) : and(x0, y) = and(y, x0)
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
              in
                x_case(x)
              .

            def and1 (x : Bool) (y : Bool) : Bool :=
              let
                bool_ind x_case (x1 : Bool) : Bool
                  | false => false
                  | true => y
                  .
              in
                x_case(x)
              .

            def first_false1 (y: Bool) : and1(false, y) = false := refl false.
            bool_ind second_false1 (x: Bool) : and1(x, false) = false
              | false => (refl false : and1(false, false) = false)
              | true => (refl false : and1(true, false) = false)
              .

            def first_true1 (y: Bool) : and1(true, y) = y := refl y.
            bool_ind second_true1 (x: Bool) : and1(x, true) = x
              | false => (refl false : and1(false, true) = false)
              | true => (refl true : and1(true, true) = true)
              .

            def and_commutative1 (x : Bool) (y : Bool) : and1(x, y) = and1(y, x) :=
              let
                bool_ind x_case(x0 : Bool) : and1(x0, y) = and1(y, x0)
                  | false =>
                      let
                        def left_is_false : and1(false, y) = false := first_false1(y).
                        def right_is_false : and1(y, false) = false := second_false1(y).
                      in
                        refl false
                  | true =>
                      let
                        def left_is_y : and1(true, y) = y := first_true1(y).
                        def right_is_y : and1(y, true) = y := second_true1(y).
                      in
                        refl y
                  .
              in
                x_case(x)
              .

            def and2 (x : Bool) (y : Bool) : Bool :=
              let
                bool_ind x_case (x1 : Bool) : Bool
                  | false => false
                  | true => y
                  .
              in
                x_case(x)
              .

            def first_false2 (y: Bool) : and2(false, y) = false := refl false.
            bool_ind second_false2 (x: Bool) : and2(x, false) = false
              | false => (refl false : and2(false, false) = false)
              | true => (refl false : and2(true, false) = false)
              .

            def first_true2 (y: Bool) : and2(true, y) = y := refl y.
            bool_ind second_true2 (x: Bool) : and2(x, true) = x
              | false => (refl false : and2(false, true) = false)
              | true => (refl true : and2(true, true) = true)
              .

            def and_commutative2 (x : Bool) (y : Bool) : and2(x, y) = and2(y, x) :=
              let
                bool_ind x_case(x0 : Bool) : and2(x0, y) = and2(y, x0)
                  | false =>
                      let
                        def left_is_false : and2(false, y) = false := first_false2(y).
                        def right_is_false : and2(y, false) = false := second_false2(y).
                      in
                        refl false
                  | true =>
                      let
                        def left_is_y : and2(true, y) = y := first_true2(y).
                        def right_is_y : and2(y, true) = y := second_true2(y).
                      in
                        refl y
                  .
              in
                x_case(x)
              .
        "};
        check(&src);
    }
}
