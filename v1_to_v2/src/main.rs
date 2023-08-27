mod ast_v1;
mod error;
mod source_display;
use askama::Template;
use lalrpop_util::lalrpop_mod;
lalrpop_mod!(
    #[allow(unused)]
    grammar_v1
);

use crate::ast_v1::*;
use crate::error::*;
use crate::grammar_v1::*;
use crate::source_display::*;
use clap::Parser;
use std::collections::BTreeMap;
use std::error::Error;
use std::fs::read_to_string;
use std::path::PathBuf;

struct WhipeCommentsOutput {
    whiped_source: String,
    comments: BTreeMap<Location, String>,
}

fn whipe_comments(source: &str) -> WhipeCommentsOutput {
    let mut comments: BTreeMap<Location, String> = BTreeMap::new();
    let whiped_lines: Vec<String> = source
        .lines()
        .map(|line| {
            if let Some(i) = line.find("//") {
                let line_begin: usize = line.as_ptr() as usize - source.as_ptr() as usize;
                let line_end: usize = line_begin + line.len();
                let comment_loc = Location(line_begin + i, line_end);
                let comment = line[i..].to_string();
                comments.insert(comment_loc, comment);

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
    let whiped_source = whiped_lines.join("\n");
    WhipeCommentsOutput {
        whiped_source,
        comments,
    }
}

fn parse(source: &str) -> Result<Vec<Decl>, CompileError> {
    ModuleParser::new()
        .parse(&mut TermUniverse::new(), source)
        .map_err(CompileError::from)
}

/// Simple program to greet a person
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    file: PathBuf,
}

fn main() -> Result<(), Box<dyn Error>> {
    let Args { file: file_path } = Args::parse();

    let v1_source = read_to_string(&file_path)?;
    let WhipeCommentsOutput {
        whiped_source: whiped_v1_source,
        comments,
    } = whipe_comments(v1_source.as_str());

    let decls = parse(whiped_v1_source.as_str()).map_err(|error| CompileErrorWithContext {
        error,
        source: v1_source.clone(),
        source_path: file_path.clone(),
    })?;

    for decl in decls {
        println!("{}", decl.render().unwrap());
    }

    Ok(())
}
