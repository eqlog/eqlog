extern crate lalrpop;
extern crate cmake;
use cmake::Config;

fn main() {
    lalrpop::process_root().unwrap();

    let dst = Config::new("phl").build();       

    println!("cargo:rustc-link-search=native={}", dst.display());
    println!("cargo:rustc-link-lib=static=phl");   
    println!("cargo:rustc-link-lib=static=stdc++");
} 
