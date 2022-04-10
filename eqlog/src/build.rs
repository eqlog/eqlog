use crate::ast::*;
use crate::error::*;
use crate::flat_ast::*;
use crate::grammar::*;
use crate::index_selection::*;
use crate::query_action::*;
use crate::rust_gen::*;
use crate::signature::*;
use crate::unification::*;
use convert_case::{Case, Casing};
use std::env;
use std::error::Error;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::{exit, Command};

fn parse(
    src: String,
) -> Result<(Signature, Vec<(Axiom, TermMap<String>)>), CompileErrorWithSource> {
    match TheoryParser::new().parse(&mut TermUniverse::new(), &src) {
        Ok(x) => Ok(x),
        Err(parse_error) => {
            let error = CompileError::from(parse_error);
            Err(CompileErrorWithSource { error, source: src })
        }
    }
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

fn process_file(name: &str, in_file: &Path, out_file: &Path) -> Result<(), Box<dyn Error>> {
    let src: String = fs::read_to_string(in_file)?;
    let (sig, axioms) = parse(src)?;
    let query_actions: Vec<QueryAction> = axioms
        .iter()
        .map(|(axiom, term_sorts)| {
            let flat_sequent = flatten_sequent(&axiom.sequent, term_sorts);
            QueryAction::new(&sig, &flat_sequent)
        })
        .collect();
    let index_selection = select_indices(&sig, &query_actions);

    let mut result: Vec<u8> = Vec::new();
    write_module(&mut result, name, &sig, &query_actions, &index_selection)?;
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
        if let Err(err) = process_file(&stem.to_case(Case::UpperCamel), &in_file, &out_file) {
            eprintln!("Error processing {in_file:?}: {err}");
            exit(1);
        }
    }
}
