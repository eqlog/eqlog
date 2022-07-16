use crate::ast::*;
use crate::error::*;
use crate::flat_ast::*;
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

    let query_actions: Vec<QueryAction> = module
        .iter_axioms()
        .map(|(axiom, term_sorts)| {
            let flat_sequent = flatten_sequent(&axiom.sequent, term_sorts);
            QueryAction::new(&module, &flat_sequent)
        })
        .collect();
    let index_selection = select_indices(&module, &query_actions);
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
        &index_selection,
    )?;
    fs::write(&out_file, &result)?;
    Command::new("rustfmt")
        .arg(&out_file)
        .status()
        .expect("Failed to format eqlog output");
    Ok(())
}

pub fn process_root() {
    let in_dir: PathBuf = "src".into();
    let out_dir: PathBuf = env::var("OUT_DIR").unwrap().into();

    for in_file in eqlog_files(&in_dir).unwrap() {
        let stem = in_file.file_stem().unwrap().to_str().unwrap();
        let out_file = out_dir.join(stem).with_extension("rs");
        println!("Compiling {in_file:?} into {out_file:?}");
        if let Err(err) = process_file(&in_file, &out_file) {
            eprintln!("{err}");
            exit(1);
        }
    }
}
