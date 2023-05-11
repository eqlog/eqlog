fn main() {
    lalrpop::process_root().unwrap();
    eqlog::process_root();
}
