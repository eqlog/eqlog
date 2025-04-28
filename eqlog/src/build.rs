use crate::eqlog_util::display_rel;
use crate::error::*;
use crate::flat_eqlog::*;
use crate::flatten::*;
use crate::fmt_util::FmtFn;
use crate::grammar::*;
use crate::grammar_util::*;
use crate::rust_gen::*;
use crate::semantics::*;
use anyhow::anyhow;
use anyhow::Context as _;
pub use anyhow::{Error, Result};
use convert_case::{Case, Casing};
use eqlog_eqlog::*;
use indoc::indoc;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::env;
use std::ffi::OsString;
use std::fmt::Display;
use std::fs;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::exit;
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

fn eqlog_files(root_path: &Path) -> Result<Vec<PathBuf>> {
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

        if file_type.is_dir() {
            result.extend(
                eqlog_files(&path)?
                    .into_iter()
                    .map(|p| PathBuf::from(entry.file_name()).join(p)),
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

        // TODO: We should emit an error if both a .eql and an .eqlog file exist, since both files
        // will correspond to the same rust file and module.
        if extension == "eql" || extension == "eqlog" {
            result.push(PathBuf::from(file_name));
        }
    }
    Ok(result)
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

fn read_out_digest(out_file_path: &Path) -> Option<Vec<u8>> {
    let file = File::open(out_file_path).ok()?;
    let first_line = BufReader::new(file).lines().next()?.ok()?;
    let digest_part = first_line.strip_prefix("// src-digest: ")?;
    base16ct::upper::decode_vec(digest_part.as_bytes()).ok()
}

fn display_src_digest<'a>(digest: &'a [u8]) -> impl 'a + Display {
    FmtFn(move |f| {
        let digest = base16ct::upper::encode_string(digest);
        writeln!(f, "// src-digest: {digest}")
    })
}

fn process_file<'a>(in_file: &'a Path, out_dir: &'a Path) -> Result<()> {
    let theory_name = in_file
        .file_stem()
        .unwrap()
        .to_str()
        .unwrap()
        .to_case(Case::UpperCamel);
    let out_file = out_dir
        .join(theory_name.to_case(Case::Snake))
        .with_extension("rs");
    let source = fs::read_to_string(in_file)
        .with_context(|| format!("Reading file {}", in_file.display()))?;

    let src_digest = digest_source(theory_name.as_str(), source.as_str());
    let out_digest = read_out_digest(out_file.as_path());

    // TODO: Add a check to verify that the out file hasn't been corrupted?
    if out_digest.as_ref().map(|od| od.as_slice()) == Some(src_digest.as_slice()) {
        return Ok(());
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

    let mut result: Vec<u8> = Vec::new();
    result.extend(
        display_src_digest(src_digest.as_slice())
            .to_string()
            .as_bytes(),
    );

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

    println!("cargo:rustc-link-search=native={}", out_dir.display());
    for rel in eqlog.iter_rel() {
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

        let status = Command::new("rustc")
            .arg("--crate-type=rlib")
            .arg("--out-dir")
            .arg(out_dir)
            .arg(table_out_file.as_path())
            .arg("-C")
            .arg("embed-bitcode=no")
            .arg("-C")
            .arg(format!("incremental={}", incremental_dir.display()))
            .status()
            .expect("Failed to compile table lib");
        assert!(status.success());

        let rlib_filename = format!(
            "lib{}.rlib",
            table_out_file.file_stem().unwrap().to_str().unwrap()
        );
        println!("cargo:rustc-link-lib=static:+verbatim={}", rlib_filename);
    }

    #[cfg(feature = "rustfmt")]
    match std::process::Command::new("rustfmt")
        .arg(&out_file)
        .status()
    {
        Err(_) => {
            // In all likelyhood, rustfmt is not installed. This is OK, only print an info.
            println!(
                "Failed to run rustfmt on eqlog output file {}",
                out_file.display()
            );
        }
        Ok(status) => {
            if !status.success() {
                // rustfmt started but failed.
                eprintln!(
                    "Formatting eqlog output file \"{}\" failed",
                    out_file.display()
                );
            }
        }
    }

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

#[doc(hidden)]
pub fn process(config: &Config) -> Result<()> {
    let Config { in_dir, out_dir } = config;
    let in_files = eqlog_files(&in_dir).with_context(|| {
        format!(
            "Searching for eqlog files in directory: {}",
            in_dir.display()
        )
    })?;

    for in_file in in_files {
        let out_parent = match in_file.parent() {
            Some(parent) => out_dir.clone().join(parent),
            None => out_dir.clone(),
        };
        std::fs::create_dir_all(&out_parent)?;

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
    let in_dir: PathBuf = "src".into();
    let out_dir: OsString = env::var_os("OUT_DIR").context(indoc! {"
            Error: Failed to read OUT_DIR environment variable

            process_root should only be called from build.rs via cargo.
        "})?;
    let out_dir: PathBuf = out_dir.into();

    let config = Config { in_dir, out_dir };

    if let Err(err) = process(&config) {
        eprintln!("{err}");
        exit(1);
    }

    print_cargo_set_eqlog_out_dir(config.out_dir.as_path());
    Ok(())
}
