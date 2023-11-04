use eqlog::{process, Config};
use indoc::formatdoc;
use std::fs;
use std::path::{Path, PathBuf};
use tempdir::TempDir;

fn test_case(case_src: &Path) {
    let in_dir = Path::new("error-test-source").join(case_src);
    assert!(
        in_dir.exists(),
        "Test case directory \"{}\"does not exist",
        in_dir.display()
    );
    assert!(
        in_dir.is_dir(),
        "Test case source \"{}\" is not a directory",
        in_dir.display()
    );

    let expected_error_path = in_dir.join("expected-error.txt");
    let expected_error: String = fs::read_to_string(&expected_error_path).unwrap_or_else(|err| {
        panic!(
            "Failure when reading expected error message file \"{}\": {err}",
            expected_error_path.display()
        )
    });

    let out_dir = TempDir::new("eqlog-test-out").expect("Failed to create output directory");
    let config = Config {
        in_dir,
        out_dir: PathBuf::from(out_dir.path()),
    };

    let actual_error = match process(&config) {
        Ok(()) => {
            panic!(
                "{}",
                formatdoc! {"
                \nCompilation succeeded 

                Expected error:
                {expected_error}
            "}
            );
        }
        Err(err) => format!("{err}"),
    };

    if actual_error != expected_error {
        panic!(
            "{}",
            formatdoc! {"
            \nError message do not match

            Got:
            {actual_error}

            Expected:
            {expected_error}
        "}
        );
    }
}

#[test]
fn undeclared_type() {
    test_case(Path::new("undeclared-type"));
}
#[test]
fn undeclared_predicate() {
    test_case(Path::new("undeclared-predicate"));
}
#[test]
fn undeclared_function() {
    test_case(Path::new("undeclared-function"));
}

#[test]
fn bad_case_type() {
    test_case(Path::new("bad-case-type"));
}
#[test]
fn bad_case_predicate() {
    test_case(Path::new("bad-case-predicate"));
}
#[test]
fn bad_case_function() {
    test_case(Path::new("bad-case-function"));
}
#[test]
fn bad_case_rule() {
    test_case(Path::new("bad-case-rule"));
}
#[test]
fn bad_case_variable() {
    test_case(Path::new("bad-case-variable"));
}

#[test]
fn variable_only_once_if() {
    test_case(Path::new("variable-only-once-if"));
}

#[test]
fn bad_argument_number_function_nullary() {
    test_case(Path::new("bad-argument-number-function-nullary"));
}
#[test]
fn bad_argument_number_function() {
    test_case(Path::new("bad-argument-number-function"));
}
#[test]
fn bad_argument_number_predicate_nullary() {
    test_case(Path::new("bad-argument-number-predicate-nullary"));
}
#[test]
fn bad_argument_number_predicate() {
    test_case(Path::new("bad-argument-number-predicate"));
}

#[test]
fn bad_symbol_kind_type_predicate() {
    test_case(Path::new("bad-symbol-kind-type-predicate"));
}
#[test]
fn bad_symbol_kind_predicate_function() {
    test_case(Path::new("bad-symbol-kind-predicate-function"));
}
#[test]
fn bad_symbol_kind_function_rule() {
    test_case(Path::new("bad-symbol-kind-function-rule"));
}

#[test]
fn symbol_declared_twice_type_pred() {
    test_case(Path::new("symbol-declared-twice-type-pred"));
}
#[test]
fn symbol_declared_twice_func_rule() {
    test_case(Path::new("symbol-declared-twice-func-rule"));
}

#[test]
fn if_after_then() {
    test_case(Path::new("if-after-then"));
}

#[test]
fn undetermined_variable_type() {
    test_case(Path::new("undetermined-variable-type"));
}

#[test]
fn conflicting_term_type_equality() {
    test_case(Path::new("conflicting-term-type-equality"));
}
#[test]
fn conflicting_term_type_app_result() {
    test_case(Path::new("conflicting-term-type-app-result"));
}
#[test]
fn conflicting_term_type_app_arg() {
    test_case(Path::new("conflicting-term-type-app-arg"));
}

#[test]
fn variable_introduced_in_then_statement() {
    test_case(Path::new("variable-introduced-in-then-statement"));
}

#[test]
fn wildcard_in_then_statement() {
    test_case(Path::new("wildcard-in-then-statement"));
}

#[test]
fn surjectivity_violation_predicate_argument() {
    test_case(Path::new("surjectivity-violation-predicate-argument"));
}
#[test]
fn surjectivity_violation_equality() {
    test_case(Path::new("surjectivity-violation-equality"));
}
#[test]
fn surjectivity_violation_nested_application() {
    test_case(Path::new("surjectivity-violation-nested-application"));
}

#[test]
fn surjectivity_violation_in_then_defined() {
    test_case(Path::new("surjectivity-violation-in-then-defined"));
}

#[test]
fn then_defined_not_variable() {
    test_case(Path::new("then-defined-not-variable"));
}
#[test]
fn then_defined_variable_not_new() {
    test_case(Path::new("then-defined-variable-not-new"));
}
