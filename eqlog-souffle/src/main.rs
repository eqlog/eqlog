#[macro_use] extern crate lalrpop_util;
lalrpop_mod!(grammar);
extern crate ena;
#[cfg(test)] #[macro_use]
extern crate maplit;
mod error;
mod ast;
mod signature;
// mod sort_inference;
// mod theory_check;
// mod emit;
// mod union_map;

// use grammar::*;
// use sort_inference::infer_sorts;
//use emit::*;
// use theory_check::check_theory;

static DUMMY_THEORY: &str = "\
Sort obj;
Sort mor;
Sort ty;
Sort tm;

Func dom : mor -> obj;
Func cod : mor -> obj;
Func comp : mor * mor -> mor;

!f =!> !dom(f);
";

fn main() {
    // let mut stdout = std::io::stdout();

    // let theory = TheoryParser::new().parse(DUMMY_THEORY).unwrap();
    // check_theory(&theory).unwrap();

    // let (r, arity) = PredicateArityParser::new().parse("R : S * T * U").unwrap();
    // let (f, dom, cod) = FunctionArityParser::new().parse("F : S * T -> U").unwrap();
    //emit_pred(&r, &arity, &mut stdout).unwrap();
    //emit_func(&f, &dom, &cod, &mut stdout).unwrap();
}
