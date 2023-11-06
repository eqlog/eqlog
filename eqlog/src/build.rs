use crate::eqlog_util::*;
use crate::error::*;
use crate::flat_eqlog::*;
use crate::flat_to_llam::*;
use crate::flatten::*;
use crate::grammar::*;
use crate::grammar_util::*;
use crate::index_selection::*;
use crate::llam::*;
use crate::rust_gen::*;
use crate::semantics::*;
use crate::sort_if_stmts_pass::*;
use crate::var_info_pass::*;
use convert_case::{Case, Casing};
use eqlog_eqlog::*;
use indoc::eprintdoc;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::env;
use std::error::Error;
use std::fs;
use std::fs::File;
use std::io;
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::{exit, Command};

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
    let mut eqlog = Eqlog::new();

    let mut identifiers: BTreeMap<String, Ident> = BTreeMap::new();
    let mut locations: BTreeMap<Location, Loc> = BTreeMap::new();

    let module = ModuleParser::new()
        .parse(&mut eqlog, &mut identifiers, &mut locations, source)
        .map_err(CompileError::from)?;

    let identifiers = identifiers.into_iter().map(|(s, i)| (i, s)).collect();
    let locations = locations
        .into_iter()
        .map(|(location, loc)| (loc, location))
        .collect();

    Ok((eqlog, identifiers, locations, module))
}

fn eqlog_files<P: AsRef<Path>>(root_dir: P) -> io::Result<Vec<PathBuf>> {
    let mut result = Vec::new();
    for entry in fs::read_dir(root_dir)? {
        let entry = entry?;
        let file_type = entry.file_type()?;

        let path = entry.path();

        if file_type.is_dir() {
            result.extend(eqlog_files(&path)?);
        }

        let is_symlink_file = || -> io::Result<bool> {
            if !file_type.is_symlink() {
                Ok(false)
            } else {
                // Ensure all symlinks are resolved
                Ok(fs::metadata(&path)?.is_file())
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

        // TODO: We should emit an error if both a .eql and an .eqlog file exist, since both files
        // will correspond to the same rust file and module.
        if extension == "eql" || extension == "eqlog" {
            result.push(path);
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

fn write_src_digest(out: &mut impl io::Write, digest: &[u8]) -> Result<(), Box<dyn Error>> {
    writeln!(
        out,
        "// src-digest: {}",
        base16ct::upper::encode_string(digest)
    )?;
    Ok(())
}

fn process_file<'a>(in_file: &'a Path, out_file: &'a Path) -> Result<(), Box<dyn Error>> {
    let theory_name = in_file
        .file_stem()
        .unwrap()
        .to_str()
        .unwrap()
        .to_case(Case::UpperCamel);
    let source = fs::read_to_string(in_file)?;

    let src_digest = digest_source(theory_name.as_str(), source.as_str());
    let out_digest = read_out_digest(out_file);

    // TODO: Add a check to verify that the out file hasn't been corrupted?
    if out_digest.as_ref().map(|od| od.as_slice()) == Some(src_digest.as_slice()) {
        return Ok(());
    }

    let source_without_comments = whipe_comments(&source);
    let (mut eqlog, identifiers, locations, _module) =
        parse(&source_without_comments).map_err(|error| CompileErrorWithContext {
            error,
            // TODO: Get rid of this copy; necessary because of the usage to create a
            // CompileErrorWithContext below.
            source: source.clone(),
            source_path: in_file.into(),
        })?;
    eqlog.close();

    check_eqlog(&eqlog, &identifiers, &locations).map_err(|error| CompileErrorWithContext {
        error,
        source: source,
        source_path: in_file.into(),
    })?;
    assert!(!eqlog.absurd());

    let _flat_rules: Vec<FlatRule> = eqlog
        .iter_rule_decl_node()
        .map(|rule| {
            let mut flat_rule = flatten_v2(rule, &eqlog, &identifiers);
            sort_if_stmts_pass(&mut flat_rule);
            let fixed_vars = fixed_vars_pass(&flat_rule);
            let _relation_infos = relation_info_pass(&fixed_vars);
            flat_rule
        })
        .collect();

    let mut query_actions: Vec<QueryAction> = Vec::new();
    query_actions.extend(
        iter_func_arities(&eqlog, &identifiers)
            .map(|(func, arity)| functionality(func, arity.as_slice())),
    );
    let rules: Vec<RuleDeclNode> = eqlog.iter_rule_decl_node().collect();
    let rule_flattenings: Vec<SequentFlattening> = rules
        .into_iter()
        .map(|rule| flatten(rule, &eqlog, &identifiers))
        .collect();
    query_actions.extend(rule_flattenings.into_iter().map(|flattening| {
        lower_sequent_seminaive(&flattening.name, &flattening.sequent, &flattening.sorts)
    }));
    let query_atoms = query_actions
        .iter()
        .map(|qa| qa.queries.iter().flatten())
        .flatten();
    let action_atoms = query_actions.iter().map(|qa| qa.action.iter()).flatten();
    let index_selection = select_indices(query_atoms, action_atoms, &eqlog, &identifiers);
    let theory_name = in_file
        .file_stem()
        .unwrap()
        .to_str()
        .unwrap()
        .to_case(Case::UpperCamel);

    let mut result: Vec<u8> = Vec::new();
    write_src_digest(&mut result, src_digest.as_slice())?;

    write_module(
        &mut result,
        &theory_name,
        &eqlog,
        &identifiers,
        &query_actions,
        &index_selection,
    )?;
    fs::write(&out_file, &result)?;
    match Command::new("rustfmt").arg(&out_file).status() {
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
pub fn process(config: &Config) -> Result<(), Box<dyn Error>> {
    let Config { in_dir, out_dir } = config;
    for in_file in eqlog_files(&in_dir)? {
        let src_rel = in_file
            .strip_prefix(&in_dir)
            .expect("File yielded by eqlog_files(dir) should be in in_dir");
        let out_parent = match src_rel.parent() {
            Some(parent) => out_dir.clone().join(parent),
            None => out_dir.clone(),
        };
        std::fs::create_dir_all(&out_parent)?;

        let name = in_file
            .file_stem()
            .expect("in_file should not be empty")
            .to_str()
            .unwrap_or_else(|| {
                eprintdoc! {"
                Input file name is not valid utf8
            "};
                exit(1)
            });
        let out_file = out_parent.join(name).with_extension("rs");

        process_file(&in_file, &out_file)?;
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
pub fn process_root() {
    let in_dir: PathBuf = "src".into();
    let out_dir: PathBuf = env::var("OUT_DIR")
        .unwrap_or_else(|err| {
            match err {
                env::VarError::NotPresent => {
                    eprintdoc! {"
                        Error: OUT_DIR environment variable not set
                        
                        process_root should only be called from build.rs via cargo.
                "};
                }
                env::VarError::NotUnicode(_) => {
                    eprintdoc! {"
                        Error: OUT_DIR environment variable is not valid utf8
                    "};
                }
            }
            exit(1)
        })
        .into();

    let config = Config { in_dir, out_dir };

    if let Err(err) = process(&config) {
        eprintln!("{err}");
        exit(1);
    }

    print_cargo_set_eqlog_out_dir(config.out_dir.as_path());
}
