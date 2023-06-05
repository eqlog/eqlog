use eqlog_runtime::eqlog_mod;
use lalrpop_util::lalrpop_mod;
eqlog_mod!(program);
mod grammar_util;
lalrpop_mod!(grammar);
#[allow(dead_code)]
mod debugging;

use crate::debugging::*;
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
        eprintln!("Type checking error");
        return ExitCode::FAILURE;
    }

    for (_, var) in p.iter_variable_expr_node() {
        if p.iter_var_type_in_expr()
            .find(|(var0, _, _)| *var0 == var)
            .is_none()
        {
            eprintln!("Usage of Undeclared variable");
            return ExitCode::FAILURE;
        }
    }

    let id3_type = var_type(*literals.vars.get("id3").unwrap(), &p);
    println!("id3 type:");
    print_type(id3_type, &p, Indent(0));

    let u_type = var_type(*literals.vars.get("u").unwrap(), &p);
    println!("u type:");
    print_type(u_type, &p, Indent(0));

    ExitCode::SUCCESS
}
