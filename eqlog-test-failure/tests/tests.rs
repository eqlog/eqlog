use eqlog::{process, Config};
use indoc::formatdoc;
use std::fs;
use std::path::{Path, PathBuf};
use tempdir::TempDir;

fn test_case(case_src: &Path) {
    let in_dir = Path::new("test-source").join(case_src);
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

    let actual_error = match process(config) {
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
