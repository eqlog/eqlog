use eqlog::{process, Config};
use indoc::indoc;
use std::fs;
use std::path::PathBuf;
use tempdir::TempDir;

fn compile_source(src: &str) {
    let in_dir = TempDir::new("eqlog-success-test-in").expect("Failed to create input directory");
    let out_dir =
        TempDir::new("eqlog-success-test-out").expect("Failed to create output directory");

    fs::write(in_dir.path().join("theory.eql"), src).expect("Failed to write source file");

    let config = Config {
        in_dir: PathBuf::from(in_dir.path()),
        out_dir: PathBuf::from(out_dir.path()),
        component_build: None,
    };
    process(&config).expect("Eqlog compilation failed");
}

#[test]
fn enum_constructor_defined_then_compiles() {
    compile_source(indoc! {"
        enum Foo {
            Bar()
        }

        rule {
            then Bar()!;
        }
    "});
}
