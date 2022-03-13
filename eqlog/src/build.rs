use crate::flat_ast::*;
use crate::grammar::*;
use crate::index_selection::*;
use crate::query_action::*;
use crate::rust_gen::*;
use std::env;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;

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

fn process_file(in_file: PathBuf, out_file: PathBuf) -> io::Result<()> {
    let src: String = fs::read_to_string(in_file)?;
    let (sig, axioms) = TheoryParser::new().parse(&src).unwrap();
    let query_actions: Vec<QueryAction> = axioms
        .iter()
        .map(|(sequent, term_sorts)| {
            let flat_sequent = flatten_sequent(sequent, term_sorts);
            QueryAction::new(&sig, &flat_sequent)
        })
        .collect();
    let index_selection = select_indices(&sig, &query_actions);

    let mut result: Vec<u8> = Vec::new();
    write_theory(
        &mut result,
        "Theory",
        &sig,
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

pub fn process_root() -> io::Result<()> {
    let in_dir: PathBuf = "src".into();
    let out_dir: PathBuf = env::var("OUT_DIR").unwrap().into();

    for in_file in eqlog_files(&in_dir)? {
        println!("Processing file {:?}", &in_file);
        let out_file = out_dir
            .join(in_file.strip_prefix(&in_dir).unwrap())
            .with_extension("rs");
        println!("Output file: {:?}", &out_file);
        process_file(in_file, out_file)?;
    }
    Ok(())
}
