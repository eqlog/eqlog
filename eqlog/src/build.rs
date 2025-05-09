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
use indoc::{formatdoc, indoc};
use rayon::iter::ParallelBridge as _;
use rayon::iter::ParallelIterator as _;
use sha2::{Digest as _, Sha256};
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
    let extensions = ["eql"];
    find_files_by_extension(root_path, &extensions)
}

// TODO: The digest mechanism is not very robust. We aren't careful about fsyncing in the right
// moments etc.
type Digest = [u8; 32];

fn digest_source(theory_name: &str, src: &str) -> Digest {
    let mut digest = Digest::default();
    Sha256::new()
        .chain_update(env!("EQLOG_SOURCE_DIGEST").as_bytes())
        .chain_update(theory_name.as_bytes())
        .chain_update(src.as_bytes())
        .finalize_into((&mut digest).into());
    digest
}

fn component_out_dir(in_file: &Path, config: &ComponentConfig) -> PathBuf {
    config.component_out_dir.join(in_file)
}

fn print_cargo_link_directives(in_file: &Path, config: Option<&ComponentConfig>) -> Result<()> {
    let config = match config {
        Some(config) => config,
        None => return Ok(()),
    };
    let comp_out_dir = component_out_dir(in_file, config);
    println!("cargo:rustc-link-search=native={}", comp_out_dir.display());
    for entry in fs::read_dir(comp_out_dir)? {
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

fn module_out_path(in_file: &Path, config: &Config) -> PathBuf {
    let module_parent = match in_file.parent() {
        None => config.out_dir.clone(),
        Some(p) => config.out_dir.join(p),
    };

    let theory_name = in_file
        .file_stem()
        .unwrap()
        .to_str()
        .unwrap()
        .to_case(Case::Snake);

    module_parent.join(format!("{theory_name}.eql.rs"))
}

fn parse_digest_hex(digest_hex: &[u8]) -> Option<Digest> {
    let mut digest: Digest = [0; 32];
    let digest_len = digest.len();
    // Invalid digests might happen if we have previously crashed after creating the digest
    // file but before writing all of the digest to it.
    // Shouldn't happen too often though, so print a warning in case it goes wrong
    // every time.
    // TODO: Need to use the cargo warn directive.
    let warning = "Ignoring digest with invalid format";
    match base16ct::upper::decode(&digest_hex, digest.as_mut_slice()) {
        Ok(out_slice) => {
            if out_slice.len() != digest_len {
                eprintln!("{warning}");
                return None;
            }
        }
        Err(_) => {
            eprintln!("{warning}");
            return None;
        }
    }

    Some(digest)
}

fn digest_file_path(in_file: &Path, config: &Config) -> PathBuf {
    match &config.component_build {
        Some(component_config) => {
            // For component builds, the digest is in a separate file.
            let theory_name = in_file
                .file_stem()
                // TODO: Do we catch this somewhere up the call stack?
                .expect("Eqlog files must have file stem")
                .to_str()
                .unwrap()
                .to_case(Case::Snake);
            let digest_file = component_config
                .component_out_dir
                .join(in_file)
                .join(format!("{theory_name}.digest"));
            digest_file
        }
        None => {
            // For module builds, the digest is in a comment on th last line of the generated module.
            module_out_path(in_file, config)
        }
    }
}

fn read_digest(in_file: &Path, config: &Config) -> Result<Option<Digest>> {
    if let Some(_) = &config.component_build {
        let content = match fs::read(digest_file_path(in_file, config).as_path()) {
            Ok(content) => content,
            Err(err) if err.kind() == ErrorKind::NotFound => {
                return Ok(None);
            }
            Err(err) => {
                return Err(err).context("Reading digest file");
            }
        };

        let digest = parse_digest_hex(&content);
        Ok(digest)
    } else {
        // For non-component builds, read from the last line of the module out file
        let module_path = module_out_path(in_file, config);

        if !module_path.exists() {
            return Ok(None);
        }

        // TODO: No need to read the whole line; we know exactly how long the digest should be, so
        // we can just seek.
        let content = fs::read_to_string(&module_path)
            .with_context(|| format!("Reading module file {}", module_path.display()))?;

        let lines: Vec<&str> = content.lines().collect();
        let last_line = match lines.last() {
            Some(last_line) => last_line,
            None => {
                return Ok(None);
            }
        };
        let hex_digest = match last_line.strip_prefix("// DIGEST: ") {
            Some(hex_digest) => hex_digest,
            None => {
                return Ok(None);
            }
        };
        let digest = parse_digest_hex(hex_digest.as_bytes());
        Ok(digest)
    }
}

fn write_digest(in_file: &Path, config: &Config, digest: &[u8]) -> Result<()> {
    let encoded_digest = base16ct::upper::encode_string(digest);

    if let Some(component_config) = &config.component_build {
        // For component builds, write to the digest file in component out dir
        let theory_name = in_file
            .file_stem()
            .unwrap()
            .to_str()
            .unwrap()
            .to_case(Case::Snake);
        let digest_file = component_config
            .component_out_dir
            .join(in_file)
            .join(format!("{theory_name}.digest"));

        fs::write(&digest_file, &encoded_digest)
            .with_context(|| format!("Writing digest file {}", digest_file.display()))
    } else {
        // For non-component builds, append to the module out file
        let module_path = module_out_path(in_file, config);

        if module_path.exists() {
            let mut content = fs::read_to_string(&module_path)
                .with_context(|| format!("Reading module file {}", module_path.display()))?;

            // Remove existing digest line if present
            let lines: Vec<&str> = content.lines().collect();
            if let Some(last_line) = lines.last() {
                if last_line.starts_with("// DIGEST: ") {
                    content = lines[..lines.len() - 1].join("\n") + "\n";
                }
            }

            // Append new digest line
            content.push_str(&format!("// DIGEST: {}\n", encoded_digest));

            fs::write(&module_path, content)
                .with_context(|| format!("Writing module file {}", module_path.display()))
        } else {
            Ok(())
        }
    }
}

fn remove_digest(in_file: &Path, config: &Config) -> Result<()> {
    let p = digest_file_path(in_file, config);
    match fs::remove_file(p.as_path()) {
        Ok(()) => {}
        Err(err) if err.kind() == ErrorKind::NotFound => {}
        Err(err) => {
            return Err(err)
                .with_context(|| format!("Failed to remove digest file {}", p.display()));
        }
    }
    Ok(())
}

fn compile_component_rlib(component_src_path: &Path, component_out_dir: &Path) -> Result<()> {
    let rlib_filename = format!(
        "lib{}.rlib",
        component_src_path
            .file_stem()
            .expect("component_src_path was generated by us, should have file stem")
            .to_str()
            .expect("component_src_path was generated by us, should be unicode")
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
        .arg(component_src_path)
        .arg("--crate-type=rlib")
        .arg("-o")
        .arg(component_out_dir.join(rlib_filename.as_str()))
        .arg("-C")
        .arg("embed-bitcode=no")
        .arg("-C")
        .arg(format!("opt-level={opt_level}"))
        .arg("-C")
        .arg("codegen-units=1");
    if debug {
        rustc_command.arg("-g");
    }

    let status = rustc_command.status().context("Running rustc")?;
    ensure!(status.success(), "Rustc finished with status {status}");
    Ok(())
}

fn process_file<'a>(in_file: &'a Path, config: &'a Config) -> Result<()> {
    let module_parent = match in_file.parent() {
        None => config.out_dir.clone(),
        Some(p) => config.out_dir.join(p),
    };

    fs::create_dir_all(&module_parent)
        .with_context(|| format!("Creating module directory {}", module_parent.display()))?;

    let build_type = config.build_type();

    let theory_name = in_file
        .file_stem()
        .unwrap()
        .to_str()
        .unwrap()
        .to_case(Case::Snake);
    let module_out_path = module_out_path(in_file, config);

    let source = fs::read_to_string(config.in_dir.join(in_file))
        .with_context(|| format!("Reading file {}", in_file.display()))?;

    // TODO: Build type should contribute to the source digest.
    let src_digest = digest_source(theory_name.as_str(), source.as_str());
    let out_digest = read_digest(in_file, config)?;

    if out_digest.as_ref().map(|od| od.as_slice()) == Some(src_digest.as_slice()) {
        print_cargo_link_directives(in_file, config.component_build.as_ref())?;
        return Ok(());
    }

    // We remove the digest file first here before we modify/overwrite generated files. Consider
    // what state we would end up otherwise in case we fail half-way through.
    remove_digest(in_file, config)?;

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

    let theory_name_len = theory_name.len();
    let symbol_prefix = format!("eql_{theory_name_len}_{theory_name}");

    let module_contents = display_module(
        &theory_name.to_case(Case::UpperCamel),
        &eqlog,
        &identifiers,
        flat_rules.rules(),
        flat_rules.analyses(),
        &index_selection,
        symbol_prefix.as_str(),
        build_type,
    )
    .to_string();
    fs::write(&module_out_path, module_contents.as_str())?;

    let component_config = match config.component_build.as_ref() {
        None => {
            write_digest(in_file, config, &src_digest)?;
            return Ok(());
        }
        Some(component_config) => component_config,
    };

    let component_out_dir = component_out_dir(in_file, component_config);

    let incremental_dir = component_out_dir.join("incremental");
    fs::create_dir_all(&incremental_dir)?;

    eqlog
        .iter_rel()
        .par_bridge()
        .try_for_each(|rel| -> Result<()> {
            let rel_name = display_rel(rel, &eqlog, &identifiers).to_string();
            let rel_snake = rel_name.to_case(Case::Snake);
            let table_out_file_name = format!("{symbol_prefix}_{rel_snake}.rs",);
            let table_out_file = component_out_dir.join(table_out_file_name);

            let indices = index_selection
                .get(&rel_name)
                .expect("Index selection should be present for all relations");
            let table_lib =
                display_table_lib(rel, &indices, &eqlog, &identifiers, symbol_prefix.as_str())
                    .to_string();
            fs::write(table_out_file.as_path(), table_lib)?;

            compile_component_rlib(table_out_file.as_path(), component_out_dir.as_path())?;
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
            let rule_out_file = component_out_dir.join(rule_out_file_name);

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
            compile_component_rlib(rule_out_file.as_path(), component_out_dir.as_path())?;
            Ok(())
        })?;

    write_digest(in_file, config, &src_digest)?;
    print_cargo_link_directives(in_file, Some(component_config))?;

    Ok(())
}

#[doc(hidden)]
pub struct ComponentConfig {
    pub component_out_dir: PathBuf,
}

/// [Config] and [process] are public for testing only, they shouldn't be used by third parties.
#[doc(hidden)]
pub struct Config {
    pub in_dir: PathBuf,
    pub out_dir: PathBuf,
    pub component_build: Option<ComponentConfig>,
}

impl Config {
    fn build_type(&self) -> BuildType {
        match &self.component_build {
            Some(_) => BuildType::Component,
            None => BuildType::Module,
        }
    }
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
    for rust_file_path in find_files_by_extension(in_dir, &["rs"])? {
        fs::create_dir_all(out_dir.join(rust_file_path))?;
    }
    Ok(())
}

#[doc(hidden)]
pub fn process(config: &Config) -> Result<()> {
    fs::create_dir_all(config.out_dir.as_path()).context("Creating out dir")?;
    if let Some(component_build) = &config.component_build {
        fs::create_dir_all(component_build.component_out_dir.as_path())
            .context("Creating component out dir")?;
    }

    let in_files = eqlog_files(config.in_dir.as_path())
        .with_context(|| format!("Searching for eqlog files in {}", config.in_dir.display()))?;

    for in_file in in_files {
        process_file(in_file.as_path(), config)?;
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
    let mut out_dir: PathBuf = fs::canonicalize(PathBuf::from(out_dir))?;
    let component_out_dir = out_dir.join("eqlog-components");

    let workspace_root = lowest_common_ancestor_path(in_dir.as_path(), out_dir.as_path())
        .ok_or_else(|| {
            anyhow!(formatdoc! {"
            Source and output paths do not have a common ancestor
            - Source: {src}
            - Out: {out}
        ", src=in_dir.display(), out=out_dir.display()})
        })?;
    let workspace_root_to_in_dir = in_dir
        .strip_prefix(workspace_root)
        .expect("workspace_root is ancestor of in_dir by construction");
    out_dir.push(workspace_root_to_in_dir);

    create_mod_dirs(in_dir.as_path(), out_dir.as_path()).with_context(|| {
        format!(
            "Recreating rust file module directory structure in {}",
            out_dir.display()
        )
    })?;

    let config = Config {
        in_dir,
        out_dir,
        component_build: Some(ComponentConfig { component_out_dir }),
    };

    process(&config)?;

    print_cargo_set_eqlog_out_dir(PathBuf::from(env::var("OUT_DIR").unwrap()).as_path());
    Ok(())
}
