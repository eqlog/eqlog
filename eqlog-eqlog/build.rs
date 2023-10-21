#[cfg(feature = "rebuild")]
fn main() -> std::process::ExitCode {
    use std::path::{Path, PathBuf};
    use std::process::ExitCode;

    let prebuilt_path = Path::new("prebuilt").canonicalize().unwrap();
    let config = eqlog::Config {
        in_dir: PathBuf::from("src"),
        out_dir: prebuilt_path,
    };

    if let Err(err) = eqlog::process(&config) {
        eprintln!("{err}");
        return ExitCode::FAILURE
    }

    println!("cargo:rustc-env=EQLOG_OUT_DIR={}", config.out_dir.display());
    ExitCode::SUCCESS
}


#[cfg(not(feature = "rebuild"))]
fn main() {
    use std::path::Path;

    let prebuilt_path = Path::new("prebuilt").canonicalize().unwrap();
    println!("cargo:rustc-env=EQLOG_OUT_DIR={}", prebuilt_path.display());
}
