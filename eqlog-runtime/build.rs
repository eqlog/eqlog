fn main() {
    let out_dir = std::env::var("OUT_DIR").unwrap();
    println!("cargo::metadata=OUT_DIR={out_dir}");
}
