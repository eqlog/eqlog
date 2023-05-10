mod ast;
use lalrpop_util::lalrpop_mod;
lalrpop_mod!(grammar);
use eqlog_runtime::eqlog_mod;
eqlog_mod!(type_system);
mod type_check;

use crate::grammar::ProgramParser;
use crate::type_system::TypeSystem;
use std::env;
use std::fs;
use std::process::ExitCode;
use type_check::*;

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

    let stmts: Vec<ast::Stmt> = match ProgramParser::new().parse(&contents) {
        Ok(stmts) => stmts,
        Err(err) => {
            eprintln!("Syntax error: {err}");
            return ExitCode::FAILURE;
        }
    };

    let mut ts = TypeSystem::new();
    let mut bindings: Bindings = Bindings::new();
    populate_stmts(&mut ts, &mut bindings, stmts.as_slice());

    ts.close();

    ExitCode::SUCCESS
}
