use eqlog_runtime::eqlog_mod;
use lalrpop_util::lalrpop_mod;
eqlog_mod!(program);
mod grammar_util;
lalrpop_mod!(grammar);

use crate::grammar::ProgramParser;
use crate::grammar_util::Literals;
use crate::program::*;
use std::env;
use std::fs;
use std::process::ExitCode;

fn main() -> ExitCode {
    let mut args = env::args();
    args.next();

    let file_name: String = match args.next() {
        Some(file_name) => file_name,
        None => {
            eprintln!("Usage: ts <FILE_NAME>");
            return ExitCode::FAILURE;
        }
    };

    let contents: String = match fs::read_to_string(&file_name) {
        Ok(contents) => contents,
        Err(err) => {
            eprintln!("Error reading file {file_name}: {err}");
            return ExitCode::FAILURE;
        }
    };

    let mut p = Program::new();
    let mut literals = Literals::new();

    let stmts: StmtNodeList = match ProgramParser::new().parse(&mut p, &mut literals, &contents) {
        Ok(stmts) => stmts,
        Err(err) => {
            eprintln!("Syntax error: {err}");
            return ExitCode::FAILURE;
        }
    };

    p.close();

    if p.absurd() {
        eprintln!("Type error");
        return ExitCode::FAILURE;
    }

    ExitCode::SUCCESS
}
