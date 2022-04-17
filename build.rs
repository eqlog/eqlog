extern crate lalrpop;
extern crate eqlog;

fn main() {
    lalrpop::process_root().unwrap();
    eqlog::process_root();
}
