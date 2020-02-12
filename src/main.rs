#[macro_use]
extern crate lalrpop_util;
#[macro_use]
extern crate lazy_static;
extern crate libc;

mod lang;
mod cwf;
mod model;
mod cwf_model;
mod type_checker;

use cwf_model::Cwf;
use type_checker::TypeChecker;

fn main() {
    let negb = "
def negb (b : bool) : bool :=
    elim b into (_ : bool) : bool
    | => false
    | => true
    end.";

    let negb = lang::parser::DefParser::new().parse(negb).unwrap();
    let mut model = Cwf::new();
    let mut tc = TypeChecker::new(model);
    let result = tc.check_def(&negb);
    println!("{:?}", result)
}
