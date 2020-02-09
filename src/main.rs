#[macro_use] extern crate lalrpop_util;

mod lang;

fn main() {
    let negb = "
def negb (b : bool) : bool :=
    elim b into (_ : bool) : bool
    | => false
    | => true
    end.";

    let negb = lang::parser::DefParser::new().parse(negb);
    //let a = rules::get_dptt();
    println!("{:?}", negb.unwrap());
}
