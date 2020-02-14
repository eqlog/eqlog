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
use std::fs;
use type_checker::TypeChecker;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let program = fs::read_to_string("src/example.qt")?;
    let p = lang::parser::DefParser::new().parse(program.as_str()).unwrap();
    let model = Cwf::new();
    let mut tc = TypeChecker::new(model);
    match tc.check_def(&p) {
        Ok(_) => println!("Ok"),
        Err(s) => println!("Err:\n{}", s)
    };
    Ok(())
}
