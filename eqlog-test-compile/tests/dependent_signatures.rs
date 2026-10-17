use std::fs;

use eqlog::{process, CompileOptions, Config};
use indoc::indoc;
use tempdir::TempDir;

fn rejects(source: &str, message: &str) {
    let input = TempDir::new("dependent-signatures").unwrap();
    let output = TempDir::new("dependent-signatures-out").unwrap();
    fs::write(input.path().join("theory.eql"), source).unwrap();
    let error = process(&Config {
        in_dir: input.path().to_owned(),
        out_dir: output.path().to_owned(),
        component_build: None,
        options: CompileOptions::default(),
    })
    .unwrap_err()
    .to_string();
    assert!(error.contains(message), "{error}");
}

#[test]
fn dependent_signatures_require_earlier_model_arguments() {
    rejects(
        "model M { type T; } pred p(x: m.T, m: M);",
        "undeclared symbol",
    );
    rejects("type T; pred p(x: T, y: x.T);", "a model-valued argument");
    rejects(
        "model M {} pred p(m: M, x: m.Missing);",
        "undeclared symbol",
    );
    rejects(
        "model M { type T; } const bad: g.T;",
        "earlier model argument",
    );
}

#[test]
fn rule_arguments_must_belong_to_the_declared_owner() {
    rejects(
        indoc! {"
            model M { type T; }
            pred p(a: M, b: M, x: a.T, y: b.T);
            rule {
                if a: M;
                if b: M;
                if x: a.T;
                if y: b.T;
                then p(a, b, y, x);
            }
        "},
        "conflicting types",
    );
    rejects(
        indoc! {"
            model M { type T; }
            func f(a: M, b: M, x: a.T) -> b.T;
            rule {
                if a: M;
                if b: M;
                if x: a.T;
                then f(a, b, x) = x;
            }
        "},
        "conflicting types",
    );
}
