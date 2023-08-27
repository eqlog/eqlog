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
use std::fs::read_to_string;
use std::iter::once;
use std::ops::Range;
use std::path::PathBuf;
use std::process::ExitCode;

struct WhipeCommentsOutput {
    whiped_source: String,
    comments: BTreeMap<usize, String>,
}

fn whipe_comments(source: &str) -> WhipeCommentsOutput {
    let mut comments: BTreeMap<usize, String> = BTreeMap::new();
    let whiped_lines: Vec<String> = source
        .lines()
        .map(|line| {
            if let Some(i) = line.find("//") {
                let line_begin: usize = line.as_ptr() as usize - source.as_ptr() as usize;
                let comment_begin = line_begin + i;
                let comment = line[i..].to_string();
                comments.insert(comment_begin, comment);

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

fn main() -> ExitCode {
    let Args { file: file_path } = Args::parse();

    let v1_source = match read_to_string(&file_path) {
        Ok(v1_source) => v1_source,
        Err(err) => {
            let file_path = file_path.display();
            eprintln!("Error opening file {file_path}: {err}");
            return ExitCode::FAILURE;
        }
    };
    let WhipeCommentsOutput {
        whiped_source: whiped_v1_source,
        comments,
    } = whipe_comments(v1_source.as_str());

    let decls = match parse(whiped_v1_source.as_str()) {
        Ok(decls) => decls,
        Err(error) => {
            let error = CompileErrorWithContext {
                error,
                source: v1_source.clone(),
                source_path: file_path.clone(),
            };
            eprintln!("{error}");
            return ExitCode::FAILURE;
        }
    };

    let end_locs = once(0).chain(decls.iter().map(|decl| decl.location().unwrap().1));
    let mut exit_code: ExitCode = ExitCode::SUCCESS;
    for (decl, prev_end_loc) in decls.iter().zip(end_locs) {
        let Location(decl_begin, decl_end) = decl.location().unwrap();
        print!("{}", &v1_source[prev_end_loc..decl_begin]);

        match decl {
            Decl::Query(_) => {
                let err_msg = "WARNING: Unsupported Query declaration";
                eprintln!("{err_msg}");
                println!("// {err_msg}:");
                print!("{}", &v1_source[decl_begin..decl_end]);
                exit_code = ExitCode::FAILURE;
                continue;
            }
            Decl::Axiom(Axiom {
                sequent: Sequent { data, .. },
                ..
            }) => match data {
                SequentData::Implication { .. } => (),
                SequentData::Reduction { .. } => (),
                SequentData::Bireduction { .. } => {
                    let err_msg = "WARNING: Unsupported <~> Axiom declaration";
                    eprintln!("{err_msg}");
                    println!("// {err_msg}:");
                    print!("{}", &v1_source[decl_begin..decl_end]);
                    exit_code = ExitCode::FAILURE;
                    continue;
                }
            },
            Decl::Sort(_) => (),
            Decl::Func(_) => (),
            Decl::Pred(_) => (),
        }

        let orphaned_comments: Vec<&str> = comments
            .range(Range {
                start: decl_begin,
                end: decl_end,
            })
            .map(|(_, comment)| comment.as_str())
            .collect();
        if !orphaned_comments.is_empty() {
            let err_msg = "WARNING: Orphaned comments";
            eprintln!("{err_msg}");
            println!("// {err_msg}:");
            for orphan in orphaned_comments {
                println!("{orphan}");
            }
            exit_code = ExitCode::FAILURE;
        }

        print!("{}", decl.render().unwrap());
    }

    if let Some(decl) = decls.last() {
        let Location(_, decl_end) = decl.location().unwrap();
        print!("{}", &v1_source[decl_end..]);
    }

    exit_code
}
