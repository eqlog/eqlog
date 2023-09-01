use crate::ast::*;
use crate::error::*;
use crate::flat_to_llam::*;
use crate::flatten::*;
use crate::grammar::*;
use crate::index_selection::*;
use crate::llam::*;
use crate::module::*;
use crate::rust_gen::*;
use convert_case::{Case, Casing};
use std::env;
use std::error::Error;
use std::fs;
use std::io;
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

fn parse(source: &str) -> Result<Module, CompileError> {
    ModuleParser::new()
        .parse(&mut TermContext::new(), source)
        .map_err(CompileError::from)
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

        if (file_type.is_file() || is_symlink_file()?)
            && path.extension().is_some()
            && path.extension().unwrap() == "eqlog"
        {
            result.push(path);
        }
    }
    Ok(result)
}

fn process_file<'a>(in_file: &'a Path, out_file: &'a Path) -> Result<(), Box<dyn Error>> {
    let source = fs::read_to_string(in_file)?;
    let source_without_comments = whipe_comments(&source);
    let module = parse(&source_without_comments).map_err(|error| CompileErrorWithContext {
        error,
        source: source.clone(),
        source_path: in_file.into(),
    })?;

    let module_wrapper = ModuleWrapper::new(&module).map_err(|error| CompileErrorWithContext {
        error,
        source,
        source_path: in_file.into(),
    })?;

    let mut query_actions: Vec<QueryAction> = Vec::new();
    query_actions.extend(module_wrapper.symbols.iter_funcs().map(|func| {
        functionality(
            &func.name,
            module_wrapper.symbols.arity(&func.name).unwrap(),
        )
    }));
    let axiom_flattenings = module_wrapper
        .iter_axioms()
        .map(|(axiom, term_sorts)| flatten_sequent(&axiom.sequent, term_sorts).into_iter())
        .flatten();
    query_actions.extend(
        axiom_flattenings
            .map(|flattening| lower_sequent_seminaive(&flattening.sequent, &flattening.sorts)),
    );
    let query_atoms = query_actions
        .iter()
        .map(|qa| qa.queries.iter().flatten())
        .flatten();
    let action_atoms = query_actions.iter().map(|qa| qa.action.iter()).flatten();
    let index_selection = select_indices(&module_wrapper, query_atoms, action_atoms);
    let theory_name = in_file
        .file_stem()
        .unwrap()
        .to_str()
        .unwrap()
        .to_case(Case::UpperCamel);
    let mut result: Vec<u8> = Vec::new();
    // TODO: write_module needs query_actions.
    write_module(
        &mut result,
        &theory_name,
        &module_wrapper,
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
    let out_dir: PathBuf = env::var("OUT_DIR").unwrap().into();

    for in_file in eqlog_files(&in_dir).unwrap() {
        let src_rel = in_file.strip_prefix(&in_dir).unwrap();
        let out_parent = match src_rel.parent() {
            Some(parent) => out_dir.clone().join(parent),
            None => out_dir.clone(),
        };
        std::fs::create_dir_all(&out_parent).unwrap();

        let name = in_file.file_stem().unwrap().to_str().unwrap();
        let out_file = out_parent.join(name).with_extension("rs");
        println!("Compiling {in_file:?} into {out_file:?}");

        if let Err(err) = process_file(&in_file, &out_file) {
            eprintln!("{err}");
            exit(1);
        }
    }
}
