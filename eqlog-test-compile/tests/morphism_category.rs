use std::fs;

use eqlog::{process, CompileOptions, Config};
use indoc::{formatdoc, indoc};
use tempdir::TempDir;

fn check_error(source: &str, expected: &str) {
    let input = TempDir::new("eqlog-category-source").unwrap();
    let output = TempDir::new("eqlog-category-output").unwrap();
    fs::write(input.path().join("theory.eql"), source).unwrap();
    let error = process(&Config {
        in_dir: input.path().to_owned(),
        out_dir: output.path().to_owned(),
        component_build: None,
        options: CompileOptions::default(),
    })
    .unwrap_err()
    .to_string();
    assert!(
        error.contains(expected),
        "expected {expected:?}, got:\n{error}"
    );
}

#[test]
fn identity_requires_a_model_instance() {
    check_error(
        indoc! {"
        type El;
        rule {
            if x: El;
            then id(x)!;
        }
    "},
        "expected a model instance as the argument of id",
    );
    check_error(
        indoc! {"
        model M {}
        rule {
            if f: Mor(M);
            then id(f)!;
        }
    "},
        "expected a model instance as the argument of id",
    );
}

#[test]
fn composition_requires_morphisms() {
    for expression in ["x >> f", "f >> x", "x >> x"] {
        let source = formatdoc! {"
            model M {{}}
            type El;
            rule {{
                if x: El;
                if f: Mor(M);
                then f = f;
                then ({expression})!;
            }}
        "};
        check_error(&source, "expected a morphism");
    }
}

#[test]
fn composition_requires_the_same_model_type() {
    check_error(
        indoc! {"
        model M {}
        model N {}
        rule {
            if f: Mor(M);
            if g: Mor(N);
            then (f >> g)!;
        }
    "},
        "term has conflicting types",
    );
}

#[test]
fn identity_requires_exactly_one_argument() {
    for expression in ["id()", "id(m, m)"] {
        let source = formatdoc! {"
            model M {{}}
            rule {{
                if m: M;
                then {expression}!;
            }}
        "};
        check_error(&source, "unrecognized token");
    }
}

#[test]
fn new_syntax_preserves_then_restrictions() {
    check_error(
        indoc! {"
        model M {}
        rule {
            if m: M;
            then id(_) = id(m);
        }
    "},
        "wildcards must not appear in then statements",
    );
    check_error(
        indoc! {"
        model M {}
        rule {
            if f: Mor(M);
            then (f >> g)!;
        }
    "},
        "variable introduced in then statement",
    );
}

#[test]
fn nested_composition_requires_known_intermediate_morphisms() {
    check_error(
        indoc! {"
        model M {}
        rule {
            if f: Mor(M);
            if g: Mor(M);
            if h: Mor(M);
            then (f >> g >> h)!;
        }
    "},
        "term does not appear earlier in this rule",
    );
}
