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
        options: CompileOptions::default(),
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
        options: CompileOptions::default(),
    };

    let in_file_path = config.in_dir.join("theory.eql");
    let out_file_path = config.out_dir.join("theory.eql.rs");

    fs::write(in_file_path.as_path(), first_src).expect("Failed to write source file");
    process(&config).expect("Initial Eqlog compilation failed");
    let sentinel = pin_modified(&out_file_path);

    fs::write(in_file_path.as_path(), second_src).expect("Failed to write source file");
    process(&config).expect("Second Eqlog compilation failed");

    assert_ne!(
        read_modified(&out_file_path),
        sentinel,
        "The output file should have changed when the input file changed"
    );
}

#[test]
fn evaluation_mode_changes_invalidate_cache() {
    let src = indoc! {"
        type Foo;
        func identity(Foo) -> Foo;
        pred edge(Foo, Foo);

        rule transitivity {
            if edge(x, y);
            if edge(y, z);
            then edge(x, z);
        }
    "};
    let in_dir = TempDir::new("evaluation-mode-in").expect("Failed to create input directory");
    let out_dir = TempDir::new("evaluation-mode-out").expect("Failed to create output directory");
    let mut config = Config {
        in_dir: in_dir.path().to_path_buf(),
        out_dir: out_dir.path().to_path_buf(),
        component_build: None,
        options: CompileOptions::default(),
    };
    let out_file = config.out_dir.join("theory.eql.rs");
    fs::write(config.in_dir.join("theory.eql"), src).expect("Failed to write source file");

    process(&config).expect("Default compilation failed");
    for evaluation_mode in [EvaluationMode::Naive, EvaluationMode::SemiNaive] {
        let sentinel = pin_modified(&out_file);
        config.options.evaluation_mode = evaluation_mode;
        process(&config).expect("Compilation after changing evaluation mode failed");
        assert_ne!(
            read_modified(&out_file),
            sentinel,
            "Changing evaluation mode must invalidate cached output"
        );

        let sentinel = pin_modified(&out_file);
        process(&config).expect("Repeated compilation failed");
        assert_eq!(
            read_modified(&out_file),
            sentinel,
            "Unchanged options must preserve cached output"
        );
    }
}

#[test]
fn model_mode_changes_invalidate_cache() {
    let src = indoc! {"
        model Set {
            type El;
            pred marked(El);
        }
    "};
    let in_dir = TempDir::new("model-mode-in").expect("Failed to create input directory");
    let out_dir = TempDir::new("model-mode-out").expect("Failed to create output directory");
    let mut config = Config {
        in_dir: in_dir.path().to_path_buf(),
        out_dir: out_dir.path().to_path_buf(),
        component_build: None,
        options: CompileOptions::default(),
    };
    let out_file = config.out_dir.join("theory.eql.rs");
    fs::write(config.in_dir.join("theory.eql"), src).expect("Failed to write source file");

    for evaluation_mode in [EvaluationMode::SemiNaive, EvaluationMode::Naive] {
        config.options.evaluation_mode = evaluation_mode;
        process(&config).expect("Native compilation failed");
        for model_mode in [ModelMode::Desugared, ModelMode::Native] {
            let sentinel = pin_modified(&out_file);
            config.options.model_mode = model_mode;
            process(&config).expect("Compilation after changing model mode failed");
            assert_ne!(read_modified(&out_file), sentinel);

            let sentinel = pin_modified(&out_file);
            process(&config).expect("Repeated compilation failed");
            assert_eq!(read_modified(&out_file), sentinel);
        }
    }
}
