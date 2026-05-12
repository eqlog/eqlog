use eqlog::{process, Config};
use indoc::indoc;
use std::fs;
use std::path::PathBuf;
use tempdir::TempDir;

fn process_src(name: &str, src: &str) -> eqlog::Result<()> {
    let in_dir =
        TempDir::new(&format!("{name}-test-in")).expect("Failed to create input directory");
    let out_dir =
        TempDir::new(&format!("{name}-test-out")).expect("Failed to create output directory");

    let config = Config {
        in_dir: PathBuf::from(in_dir.path()),
        out_dir: PathBuf::from(out_dir.path()),
        component_build: None,
    };

    fs::write(config.in_dir.join("theory.eql"), src).expect("Failed to write source file");
    process(&config)
}

#[test]
fn member_constructor_lookup_compiles() {
    let src = indoc! {"
        model M {
            enum E {
                C()
            }
        }

        rule {
            if m: M;
            then m.C()!;
        }
    "};

    process_src("member-constructor-lookup", src).expect("Eqlog compilation failed");
}

#[test]
fn member_type_lookup_ignores_global_symbol() {
    let src = indoc! {"
        type Bar;

        model M {
            type Foo;
        }

        rule {
            if x: M;
            if y: x.Bar;
            then y = y;
        }
    "};

    let err = process_src("member-type-lookup", src).expect_err("Eqlog compilation succeeded");
    let actual = format!("{err}");
    assert!(actual.contains("undeclared symbol \"Bar\""), "{actual}");
    assert!(actual.contains("theory.eql:9"), "{actual}");
}
