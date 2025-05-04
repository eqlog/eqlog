use crate::eqlog_util::display_rel;
use crate::error::*;
use crate::flat_eqlog::*;
use crate::flatten::*;
use crate::grammar::*;
use crate::grammar_util::*;
use crate::rust_gen::*;
use crate::semantics::*;
use anyhow::anyhow;
use anyhow::ensure;
use anyhow::Context as _;
pub use anyhow::{Error, Result};
use convert_case::{Case, Casing};
use eqlog_eqlog::*;
use indoc::indoc;
use rayon::iter::ParallelBridge as _;
use rayon::iter::ParallelIterator as _;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::env;
use std::ffi::OsStr;
use std::ffi::OsString;
use std::fs::{self};
use std::io::ErrorKind;
use std::path::{Path, PathBuf};
use std::process::Command;

fn whipe_comments(source: &str) -> String {
    let lines: Vec<String> = source
        .lines()
        .map(|line| {
            if let Some(i) = line.find("//") {
                let mut l = line[0..i].to_string();
                for _ in i..line.len() {
                    l.push(' ');
                }
                l
            } else {
                line.to_string()
            }
        })
        .collect();
    lines.join("\n")
}

fn parse(
    source: &str,
) -> Result<
    (
        Eqlog,
        BTreeMap<Ident, String>,
        BTreeMap<Loc, Location>,
        ModuleNode,
    ),
    CompileError,
> {
    let source = whipe_comments(&source);
    let mut eqlog = Eqlog::new();

    let mut identifiers: BTreeMap<String, Ident> = BTreeMap::new();
    let mut locations: BTreeMap<Location, Loc> = BTreeMap::new();

    let module = ModuleParser::new()
        .parse(
            &mut eqlog,
            &mut identifiers,
            &mut locations,
            source.as_str(),
        )
        .map_err(CompileError::from)?;

    let identifiers = identifiers.into_iter().map(|(s, i)| (i, s)).collect();
    let locations = locations
        .into_iter()
        .map(|(location, loc)| (loc, location))
        .collect();

    Ok((eqlog, identifiers, locations, module))
}

fn find_files_by_extension(root_path: &Path, extensions: &[&str]) -> Result<Vec<PathBuf>> {
    let mut result = Vec::new();

    if !root_path.is_dir() {
        return Err(anyhow!("Path is not a directory: {}", root_path.is_dir()));
    }

    let entries = fs::read_dir(root_path)
        .with_context(|| format!("Reading directory: {}", root_path.display()))?;
    for entry in entries {
        let entry = entry.context("Reading directory entry")?;
        let path = entry.path();
        let file_type = entry
            .file_type()
            .with_context(|| format!("Getting file type for entry: {}", entry.path().display()))?;
        let file_name = entry.file_name();

        if file_type.is_dir() {
            result.extend(
                find_files_by_extension(&path, extensions)?
                    .into_iter()
                    .map(|p| PathBuf::from(&file_name).join(p)),
            );
        }

        let is_symlink_file = || -> Result<bool> {
            if !file_type.is_symlink() {
                Ok(false)
            } else {
                let metadata = fs::metadata(&path)
                    .with_context(|| format!("Resolving symlink: {}", path.display()))?;
                // Ensure all symlinks are resolved
                Ok(metadata.is_file())
            }
        };

        if !(file_type.is_file() || is_symlink_file()?) {
            continue;
        }

        let extension = match path.extension() {
            Some(extension) => extension,
            None => {
                continue;
            }
        };
        let file_name = path
            .file_name()
            .expect("Files with extensions always have file names");

        if extensions
            .iter()
            .find(|ext| OsStr::new(**ext) == extension)
            .is_some()
        {
            result.push(PathBuf::from(file_name));
        }
    }
    Ok(result)
}

fn eqlog_files(root_path: &Path) -> Result<Vec<PathBuf>> {
    // TODO: We should emit an error if both a .eql and an .eqlog file exist, since both files
    // will correspond to the same rust file and module.
    let extensions = ["eqlog", "eql"];
    find_files_by_extension(root_path, &extensions)
}

fn digest_source(theory_name: &str, src: &str) -> Vec<u8> {
    Sha256::new()
        .chain_update(env!("EQLOG_SOURCE_DIGEST").as_bytes())
        .chain_update(theory_name.as_bytes())
        .chain_update(src.as_bytes())
        .finalize()
        .as_slice()
        .into()
}

fn print_cargo_link_directives(out_dir: &Path) -> Result<()> {
    println!("cargo:rustc-link-search=native={}", out_dir.display());
    for entry in fs::read_dir(out_dir)? {
        let entry = entry?;
        let path = entry.path();
        if !path.is_file() {
            continue;
        }

        if path.extension() != Some(OsStr::new("rlib")) {
            continue;
        }

        let file_name = path
            .file_name()
            .expect("Path with extension always also has a file name")
            .to_str()
            .expect("Eqlog generates unicode filenames only");
        println!("cargo:rustc-link-lib=static:+verbatim={}", file_name);
    }
    Ok(())
}

fn process_file<'a>(in_file: &'a Path, out_dir: &'a Path) -> Result<()> {
    let theory_name = in_file
        .file_stem()
        .unwrap()
        .to_str()
        .unwrap()
        .to_case(Case::UpperCamel);
    let out_file = out_dir.join("mod.rs");
    // TODO: The digest mechanism is not very robust. We aren't careful about fsyncing in the right
    // moments etc.
    let digest_file = out_dir.join(format!("{theory_name}.digest"));
    let source = fs::read_to_string(in_file)
        .with_context(|| format!("Reading file {}", in_file.display()))?;

    let src_digest = digest_source(theory_name.as_str(), source.as_str());
    let out_digest: Option<Vec<u8>> = match fs::read(digest_file.as_path()) {
        Ok(content) => base16ct::upper::decode_vec(&content).ok(),
        Err(err) if err.kind() == ErrorKind::NotFound => None,
        Err(err) => {
            return Err(err)
                .with_context(|| format!("Failed to read digest file {}", digest_file.display()));
        }
    };

    if out_digest.as_ref().map(|od| od.as_slice()) != Some(src_digest.as_slice()) {
        // We remove the digest file first here before we modify/overwrite generated files. Consider
        // what state we would end up otherwise in case we fail half-way through.
        match fs::remove_file(digest_file.as_path()) {
            Ok(()) => {}
            Err(err) if err.kind() == ErrorKind::NotFound => {}
            Err(err) => {
                // Propagate other errors (e.g., permissions)
                return Err(err).with_context(|| {
                    format!(
                        "Failed to remove outdated digest file {}",
                        digest_file.display()
                    )
                });
            }
        }

        let (mut eqlog, identifiers, locations, _module) = match parse(source.as_str()) {
            Ok(x) => x,
            Err(error) => {
                return Err(CompileErrorWithContext {
                    error,
                    source,
                    source_path: in_file.into(),
                }
                .into());
            }
        };
        eqlog.close();

        check_eqlog(&eqlog, &identifiers, &locations).map_err(|error| CompileErrorWithContext {
            error,
            source,
            source_path: in_file.into(),
        })?;
        assert!(!eqlog.absurd());

        let flat_rules = flatten(&eqlog, &identifiers);

        let index_selection = select_indices(flat_rules.analyses(), &eqlog, &identifiers);

        let theory_name = in_file
            .file_stem()
            .unwrap()
            .to_str()
            .unwrap()
            .to_case(Case::UpperCamel);

        let theory_name_snake = theory_name.to_case(Case::Snake);
        let theory_name_len = theory_name_snake.len();
        let symbol_prefix = format!("eql_{theory_name_len}_{theory_name_snake}");

        let result = display_module(
            &theory_name,
            &eqlog,
            &identifiers,
            flat_rules.rules(),
            flat_rules.analyses(),
            &index_selection,
            symbol_prefix.as_str(),
        )
        .to_string();
        fs::write(&out_file, &result)?;

        let incremental_dir = out_dir.join("incremental");
        fs::create_dir_all(&incremental_dir)?;

        eqlog.iter_rel().par_bridge().try_for_each(|rel| {
            let rel_name = display_rel(rel, &eqlog, &identifiers).to_string();
            let rel_snake = rel_name.to_case(Case::Snake);
            let table_out_file_name = format!("{symbol_prefix}_{rel_snake}.rs",);
            let table_out_file = out_dir.join(table_out_file_name);

            let indices = index_selection
                .get(&rel_name)
                .expect("Index selection should be present for all relations");
            let table_lib =
                display_table_lib(rel, &indices, &eqlog, &identifiers, symbol_prefix.as_str())
                    .to_string();
            fs::write(table_out_file.as_path(), table_lib)?;

            let rlib_filename = format!(
                "lib{}.rlib",
                table_out_file
                    .file_stem()
                    .expect("table_out_file was generated by us, should have file stem")
                    .to_str()
                    .expect("table_out_file was generated by us, should be unicode")
            );

            let rustc_path: PathBuf = env::var_os("RUSTC")
                .context("Reading RUSTC environment variable")?
                .into();

            let debug_var = env::var("DEBUG").context("Reading DEBUG env var")?;
            let debug = match debug_var.as_str() {
                "true" => true,
                "false" => false,
                _ => {
                    return Err(anyhow!("Invalid DEBUG var value: {debug_var}"));
                }
            };

            let opt_level = env::var("OPT_LEVEL").context("Reading OPT_LEVEL env var")?;

            let mut rustc_command = Command::new(rustc_path);
            rustc_command
                .arg(table_out_file.as_path())
                .arg("--crate-type=rlib")
                .arg("-o")
                .arg(out_dir.join(rlib_filename.as_str()))
                .arg("-C")
                .arg("embed-bitcode=no")
                .arg("-C")
                .arg(format!("opt-level={opt_level}"))
                .arg("-C")
                .arg("codegen-units=1")
                .arg("-C")
                .arg(format!("incremental={}", incremental_dir.display()));
            if debug {
                rustc_command.arg("-g");
            }

            let status = rustc_command.status().context("Running rustc")?;
            ensure!(status.success(), "Rustc finished with status {status}");
            Ok(())
        })?;

        flat_rules
            .rules()
            .iter()
            .zip(flat_rules.analyses())
            .par_bridge()
            .try_for_each(|(rule, analysis)| -> Result<()> {
                let rule_name_snake = rule.name.to_case(Case::Snake);
                let rule_out_file_name = format!("{symbol_prefix}_{rule_name_snake}.rs");
                let rule_out_file = out_dir.join(rule_out_file_name);

                let rule_lib = display_rule_lib(
                    rule,
                    analysis,
                    &index_selection,
                    &eqlog,
                    &identifiers,
                    symbol_prefix.as_str(),
                )
                .to_string();

                fs::write(rule_out_file.as_path(), rule_lib)?;

                let rlib_filename = format!(
                    "lib{}.rlib",
                    rule_out_file
                        .file_stem()
                        .expect("rule_out_file was generated by us, should have file stem")
                        .to_str()
                        .expect("rule_out_file was generated by us, should be unicode")
                );

                let rustc_path: PathBuf = env::var_os("RUSTC")
                    .context("Reading RUSTC environment variable")?
                    .into();

                let debug_var = env::var("DEBUG").context("Reading DEBUG env var")?;
                let debug = match debug_var.as_str() {
                    "true" => true,
                    "false" => false,
                    _ => {
                        return Err(anyhow!("Invalid DEBUG var value: {debug_var}"));
                    }
                };

                let opt_level = env::var("OPT_LEVEL").context("Reading OPT_LEVEL env var")?;

                let mut rustc_command = Command::new(rustc_path);
                rustc_command
                    .arg(rule_out_file.as_path())
                    .arg("--crate-type=rlib")
                    .arg("-o")
                    .arg(out_dir.join(rlib_filename.as_str()))
                    .arg("-C")
                    .arg("embed-bitcode=no")
                    .arg("-C")
                    .arg(format!("opt-level={opt_level}"))
                    .arg("-C")
                    .arg("codegen-units=1")
                    .arg("-C")
                    .arg(format!("incremental={}", incremental_dir.display()));
                if debug {
                    rustc_command.arg("-g");
                }

                let status = rustc_command.status().context("Running rustc")?;
                ensure!(status.success(), "Rustc finished with status {status}");
                Ok(())
            })?;

        let encoded_digest = base16ct::upper::encode_string(&src_digest);
        fs::write(&digest_file, encoded_digest)?;
    }

    print_cargo_link_directives(out_dir)?;
    Ok(())
}

/// [Config] and [process] are public for testing only, they shouldn't be used by third parties.
#[doc(hidden)]
pub struct Config {
    pub in_dir: PathBuf,
    pub out_dir: PathBuf,
}

#[doc(hidden)]
pub fn print_cargo_set_eqlog_out_dir(out_dir: &Path) {
    println!("cargo:rustc-env=EQLOG_OUT_DIR={}", out_dir.display());
}

pub fn lowest_common_ancestor_path<'a, 'b>(mut a: &'a Path, b: &'b Path) -> Option<&'a Path> {
    loop {
        if b.starts_with(a) {
            return Some(a);
        }

        a = match a.parent() {
            Some(p) => p,
            None => {
                break;
            }
        };
    }

    None
}

fn create_mod_dirs(in_dir: &Path, out_dir: &Path) -> Result<()> {
    let workspace_root = lowest_common_ancestor_path(in_dir, out_dir)
        .expect("TODO: Handle in_dir and out_dir not having common ancestor");
    for rust_file_path in find_files_by_extension(in_dir, &["rs"])? {
        let rust_file_path = in_dir.join(rust_file_path);
        let rust_file_path = rust_file_path
            .strip_prefix(workspace_root)
            .expect("should have workspace_root <= in_dir <= rust_file_path");
        fs::create_dir_all(out_dir.join(rust_file_path))?;
    }
    Ok(())
}

#[doc(hidden)]
pub fn process(config: &Config) -> Result<()> {
    let Config { in_dir, out_dir } = config;
    let in_dir = fs::canonicalize(in_dir.as_path())
        .with_context(|| anyhow!("Canonicalizing input directory: {}", in_dir.display()))?;
    let out_dir = fs::canonicalize(out_dir.as_path())
        .with_context(|| anyhow!("Canonicalizing output directory: {}", out_dir.display()))?;

    println!("cargo::rerun-if-changed={}", in_dir.display());

    create_mod_dirs(in_dir.as_path(), out_dir.as_path()).with_context(|| {
        format!(
            "Recreating rust file module directory structure in {}",
            out_dir.display()
        )
    })?;

    let in_files = eqlog_files(&in_dir)
        .with_context(|| format!("Searching for eqlog files in  {}", in_dir.display()))?;

    let workspace_root = lowest_common_ancestor_path(in_dir.as_path(), out_dir.as_path())
        .ok_or_else(|| anyhow!("input and output directory don't have a common ancestor"))?;

    for in_file in in_files {
        let in_file = in_dir.join(in_file);
        let out_parent = out_dir.join(in_file.strip_prefix(workspace_root).unwrap());
        fs::create_dir_all(&out_parent)
            .with_context(|| format!("Creating output directory {}", out_parent.display()))?;

        process_file(in_dir.join(in_file).as_path(), &out_parent)?;
    }

    Ok(())
}

/// Compile all eqlog files in the `src` directory into rust modules.
///
/// Must be called from a `build.rs` script via cargo.
/// Output rust files are written to the cargo target out directory.
/// Exits the process on compilation failure.
///
/// # Examples
/// ```
/// fn main() {
///     eqlog::process_root();
/// }
/// ```
pub fn process_root() -> Result<()> {
    let in_dir: PathBuf = fs::canonicalize(Path::new("src"))?;
    let out_dir: OsString = env::var_os("OUT_DIR").context(indoc! {"
            Error: Failed to read OUT_DIR environment variable

            process_root should only be called from build.rs via cargo.
        "})?;
    let out_dir: PathBuf = fs::canonicalize(PathBuf::from(out_dir))?;

    let config = Config { in_dir, out_dir };

    process(&config)?;

    print_cargo_set_eqlog_out_dir(PathBuf::from(env::var("OUT_DIR").unwrap()).as_path());
    Ok(())
}
