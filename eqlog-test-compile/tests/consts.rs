use eqlog::{process, Config};
use indoc::indoc;
use std::fs;
use std::path::PathBuf;
use tempdir::TempDir;

fn compile(src: &str) {
    let in_dir = TempDir::new("eqlog-const-test-in").expect("Failed to create input directory");
    let out_dir = TempDir::new("eqlog-const-test-out").expect("Failed to create output directory");
    let config = Config {
        in_dir: PathBuf::from(in_dir.path()),
        out_dir: PathBuf::from(out_dir.path()),
        component_build: None,
    };

    fs::write(config.in_dir.join("theory.eql"), src).expect("Failed to write test source");
    process(&config).expect("Eqlog compilation failed");
}

#[test]
fn ambient_const_declaration() {
    compile(indoc! {"
        type El;
        const foo: El;
        pred present(El);

        rule {
            then foo!;
        }

        rule {
            if foo!;
            then present(foo);
        }

        rule {
            if foo!;
            then x := foo!;
            then present(x);
        }
    "});
}

#[test]
fn member_const_declaration() {
    compile(indoc! {"
        model Container {
            type Elem;
            const inner: Elem;
            pred inner_present(Elem);

            rule {
                then inner!;
            }

            rule {
                if inner!;
                then inner_present(inner);
            }
        }

        rule {
            if c: Container;
            if c.inner!;
            then c.inner = c.inner;
        }
    "});
}

#[test]
fn binder_can_shadow_const() {
    compile(indoc! {"
        type El;
        const foo: El;
        pred present(El);

        rule {
            if foo: El;
            then present(foo);
        }
    "});
}
