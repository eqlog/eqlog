extern crate eqlog;
extern crate lalrpop;

fn main() {
    lalrpop::process_root().unwrap();
    eqlog::process_root();
}
