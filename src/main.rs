#[macro_use]
extern crate lalrpop_util;
#[macro_use]
extern crate lazy_static;
extern crate libc;
extern crate scopeguard;

mod lang;
mod cwf;
mod model;
mod cwf_model;
mod type_checker;

use cwf_model::Cwf;
use type_checker::TypeChecker;

fn main() {
    let p = "def id (b : bool) (c : b = b) : b = b := c.";
    let p = lang::parser::DefParser::new().parse(p).unwrap();
    let mut model = Cwf::new();
    let mut tc = TypeChecker::new(model);
    let result = tc.check_def(&p);
    println!("{:?}", result)
}
