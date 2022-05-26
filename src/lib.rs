#![recursion_limit = "128"]
extern crate eqlog_util;
#[cfg(test)]
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

use crate::cwf_checker::*;
use crate::grammar::UnitParser;
#[cfg(test)]
use indoc::indoc;

fn check(source: &str) {
    let defs = UnitParser::new().parse(source).unwrap();

    let mut scope = Scope::new();
    for def in defs.iter() {
        scope.add_definition(Checking::Yes, def);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unit_identity() {
        let src = indoc! {"
            def id(x: Unit) : Unit := x.
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
            unit_ind unique_based (x : Unit) : x = unit
              | unit => (refl unit : unit = unit)
              .
        "};
        check(&src);
    }

    #[test]
    fn test_app_unit_uniqueness() {
        let src = indoc! {"
            unit_ind unique_based (x : Unit) : x = unit
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
}
