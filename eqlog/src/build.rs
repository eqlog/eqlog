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
use indoc::indoc;
use std::env;
use std::error::Error;
use std::fs;
use std::io;
use std::iter::once;
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
        .parse(&mut TermUniverse::new(), source)
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
        source,
        source_path: in_file.into(),
    })?;

    let mut query_actions: Vec<QueryAction> = Vec::new();
    query_actions.extend(
        module
            .iter_functions()
            .map(|Function { name, dom, cod, .. }| {
                let arity: Vec<&str> = dom.iter().chain(once(cod)).map(|s| s.as_str()).collect();
                functionality(name, &arity)
            }),
    );
    query_actions.extend(module.iter_axioms().map(|(axiom, term_sorts)| {
        let flat_sequent = flatten_sequent(&axiom.sequent, term_sorts);
        lower_sequent_seminaive(&module, &flat_sequent)
    }));
    let pure_queries: Vec<(String, PureQuery)> = module
        .iter_queries()
        .map(|(query, term_sorts)| {
            let flat_query = flatten_query(&query, term_sorts);
            (query.name.clone(), lower_query(&module, &flat_query))
        })
        .collect();
    let query_atoms = query_actions
        .iter()
        .map(|qa| qa.queries.iter().flatten())
        .flatten()
        .chain(
            pure_queries
                .iter()
                .map(|(_, pq)| pq.queries.iter().flatten())
                .flatten(),
        );
    let action_atoms = query_actions.iter().map(|qa| qa.action.iter()).flatten();
    let index_selection = select_indices(&module, query_atoms, action_atoms);
    let theory_name = in_file
        .file_stem()
        .unwrap()
        .to_str()
        .unwrap()
        .to_case(Case::UpperCamel);
    let mut result: Vec<u8> = Vec::new();
    write_module(
        &mut result,
        &theory_name,
        &module,
        &query_actions,
        &pure_queries,
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

pub fn process_root() -> io::Result<()> {
    let in_dir: PathBuf = "src".into();
    let out_dir: PathBuf = env::var("OUT_DIR")
        .map_err(|_| {
            io::Error::new(
                io::ErrorKind::Other,
                indoc! {"
                Failed to read $OUT_DIR environment variable.
                eqlog::process_root must be run via cargo in a build.rs script.
            "},
            )
        })?
        .into();

    for in_file in eqlog_files(&in_dir)? {
        let src_rel = in_file.strip_prefix(&in_dir).unwrap();
        let out_parent = match src_rel.parent() {
            Some(parent) => out_dir.clone().join(parent),
            None => out_dir.clone(),
        };
        std::fs::create_dir_all(&out_parent)?;

        let name = in_file.file_stem().unwrap().to_str()?;
        let out_file = out_parent.join(name).with_extension("rs");
        println!("Compiling {in_file:?} into {out_file:?}");

        if let Err(err) = process_file(&in_file, &out_file) {
            eprintln!("{err}");
            exit(1);
        }
    }
    Ok(())
}
