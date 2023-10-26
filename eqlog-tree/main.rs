use eqlog_tree::{process, Config};
use std::env;
use std::path::PathBuf;

fn main() {
    let mut args = env::args();
    args.next().unwrap();
    let in_dir = PathBuf::from(args.next().unwrap());
    let out_dir = PathBuf::from(args.next().unwrap());
    let config = Config { in_dir, out_dir };
    process(&config).unwrap();
}
