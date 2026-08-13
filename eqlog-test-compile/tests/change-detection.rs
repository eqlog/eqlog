use eqlog::*;
use indoc::indoc;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::SystemTime;
use tempdir::TempDir;

fn read_modified(path: &Path) -> SystemTime {
    fs::metadata(path)
        .expect("Failed to read output file metadata")
        .modified()
        .expect("Failed to read output file modified time")
}

// Pin to a sentinel so a skip is distinguishable from a rewrite when the
// filesystem mtime granularity is 1s.
fn pin_modified(path: &Path) -> SystemTime {
    let sentinel = SystemTime::UNIX_EPOCH;
    fs::File::open(path)
        .expect("Failed to open output file")
        .set_modified(sentinel)
        .expect("Failed to set output file modified time");
    let actual = read_modified(path);
    assert_eq!(
        actual, sentinel,
        "Filesystem did not honor the sentinel modified time"
    );
    sentinel
}

#[test]
fn unchanged_file_detected() {
    let src = indoc! {"
        type Foo;
    "};

    let in_dir =
        TempDir::new("unchanged-file-detected-test-in").expect("Failed to create input directory");
    let out_dir = TempDir::new("unchanged-file-detected-test-out")
        .expect("Failed to create output directory");

    let config = Config {
        in_dir: PathBuf::from(in_dir.path()),
        out_dir: PathBuf::from(out_dir.path()),
        component_build: None,
    };

    let in_file_path = config.in_dir.join("theory.eql");
    let out_file_path = config.out_dir.join("theory.eql.rs");

    fs::write(in_file_path.as_path(), src).expect("Failed to write source file");

    process(&config).expect("Initial Eqlog compilation failed");
    let sentinel = pin_modified(out_file_path.as_path());

    process(&config).expect("Second Eqlog compilation failed");
    let modified_second = read_modified(out_file_path.as_path());

    assert_eq!(
        modified_second, sentinel,
        "The output file should not be changed if the input file hasn't changed"
    );
}

#[test]
fn changed_file_detected() {
    let first_src = indoc! {"
        type Foo;
    "};
    let second_src = indoc! {"
        type Bar;
    "};

    let in_dir =
        TempDir::new("changed-file-detected-test-in").expect("Failed to create input directory");
    let out_dir =
        TempDir::new("changed-file-detected-test-out").expect("Failed to create output directory");

    let config = Config {
        in_dir: PathBuf::from(in_dir.path()),
        out_dir: PathBuf::from(out_dir.path()),
        component_build: None,
    };

    let in_file_path = config.in_dir.join("theory.eql");
    let out_file_path = config.out_dir.join("theory.eql.rs");

    fs::write(in_file_path.as_path(), first_src).expect("Failed to write source file");
    process(&config).expect("Initial Eqlog compilation failed");
    let first_out =
        fs::read_to_string(out_file_path.as_path()).expect("Failed to read output file");

    fs::write(in_file_path.as_path(), second_src).expect("Failed to write source file");
    process(&config).expect("Second Eqlog compilation failed");
    let second_out =
        fs::read_to_string(out_file_path.as_path()).expect("Failed to read output file");

    assert_ne!(
        first_out, second_out,
        "The output file should have changed when the input file changed"
    );
}
