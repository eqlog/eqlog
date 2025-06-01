use anyhow::{anyhow, bail, ensure, Context as _, Result};
use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

fn main() -> Result<()> {
    let rustc_path: PathBuf = env::var_os("RUSTC")
        .ok_or_else(|| anyhow!("RUSTC environment variable is not set"))?
        .into();

    let debug_var = env::var("DEBUG").context("Reading DEBUG env var")?;
    let debug = match debug_var.as_str() {
        "true" => true,
        "false" => false,
        _ => {
            bail!("Invalid DEBUG var value: {debug_var}");
        }
    };

    let opt_level = env::var("OPT_LEVEL").context("Reading OPT_LEVEL env var")?;
    let out_dir_path: PathBuf = env::var("OUT_DIR")
        .context("Reading OUT_DIR env var")?
        .into();

    let runtime_rlib_path = compile_lib_impl(&rustc_path, &out_dir_path, &opt_level, debug)?;

    println!("cargo:rustc-link-search=native={}", out_dir_path.display());
    println!(
        "cargo:rustc-link-lib=static:+verbatim={}",
        runtime_rlib_path.file_name().unwrap().to_str().unwrap()
    );
    println!("cargo::metadata=RLIB_PATH={}", runtime_rlib_path.display());

    Ok(())
}

fn compile_lib_impl(
    rustc_path: &Path,
    out_dir_path: &Path,
    opt_level: &str,
    debug: bool,
) -> Result<PathBuf> {
    let lib_rs_path = Path::new("./src/lib_impl.rs");
    let lib_impl_rlib_path = out_dir_path.join("libeqlog_runtime_impl.rlib");

    let mut rustc_command = Command::new(rustc_path);
    rustc_command
        .arg(lib_rs_path)
        .arg("--crate-name=eqlog_runtime_impl")
        .arg("--crate-type=rlib")
        .arg("-o")
        .arg(&lib_impl_rlib_path)
        .arg("-L")
        .arg(out_dir_path)
        .arg("-C")
        .arg("embed-bitcode=no")
        .arg("-C")
        .arg(format!("opt-level={}", opt_level))
        .arg("-C")
        .arg("codegen-units=1");

    if debug {
        rustc_command.arg("-g");
    }

    let status = rustc_command
        .status()
        .with_context(|| format!("Failed to execute rustc for lib_impl: {:?}", rustc_path))?;
    ensure!(
        status.success(),
        "Rustc command for lib_impl failed with status: {}",
        status
    );

    Ok(lib_impl_rlib_path)
}
