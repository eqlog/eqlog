use eqlog::*;
use indoc::indoc;
use std::fs;
use std::path::{Path, PathBuf};
use std::thread::sleep;
use std::time::{Duration, SystemTime};
use tempdir::TempDir;

fn read_modified(path: &Path) -> SystemTime {
    fs::metadata(path)
        .expect("Failed to read output file metadata")
        .modified()
        .expect("Failed to read output file modified time")
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
    };

    let in_file_path = config.in_dir.join("theory.eql");
    let out_file_path = config.out_dir.join("theory.rs");

    fs::write(in_file_path.as_path(), src).expect("Failed to write source file");

    process(&config).expect("Initial Eqlog compilation failed");
    let modified_first: SystemTime = read_modified(out_file_path.as_path());

    sleep(Duration::from_millis(1));

    process(&config).expect("Second Eqlog compilation failed");
    let modified_second: SystemTime = read_modified(out_file_path.as_path());

    let duration = modified_second
        .duration_since(modified_first)
        .expect("No duration between modified_first and modified_second -- clock anomaly?");
    assert!(
        duration.is_zero(),
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
    };

    let in_file_path = config.in_dir.join("theory.eql");
    let out_file_path = config.out_dir.join("theory.rs");

    fs::write(in_file_path.as_path(), first_src).expect("Failed to write source file");
    process(&config).expect("Initial Eqlog compilation failed");
    let modified_first: SystemTime = read_modified(out_file_path.as_path());

    sleep(Duration::from_millis(1));

    fs::write(in_file_path.as_path(), second_src).expect("Failed to write source file");
    process(&config).expect("Second Eqlog compilation failed");
    let modified_second: SystemTime = read_modified(out_file_path.as_path());

    let duration = modified_second
        .duration_since(modified_first)
        .expect("No duration between modified_first and modified_second -- clock anomaly?");
    assert!(
        !duration.is_zero(),
        "The output file should have changed when the input file changed"
    );
}
