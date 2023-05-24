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
        eprintln!("Variable scope error");
    }

    //let mut ts = TypeSystem::new();
    //let mut bindings: Bindings = Bindings::new();
    //populate_stmts(&mut ts, &mut bindings, stmts.as_slice());

    //ts.close();

    //assert!(!ts.conflict());

    //let k: type_system::Expr = ts.variable_expr(*bindings.get("k").unwrap()).unwrap();
    //let number: type_system::Ty = ts.number_ty().unwrap();
    //assert!(ts.are_equal_ty(ts.expr_ty(k).unwrap(), number));

    //let asdf: type_system::Expr = ts.variable_expr(*bindings.get("asdf").unwrap()).unwrap();
    //let asdf_ty: type_system::Ty = ts.expr_ty(asdf).unwrap();

    //let asdf_ty_dom: type_system::TyList = ts.domain(asdf_ty).unwrap();
    //let nil_tys = ts.nil_ty_list().unwrap();
    //assert!(ts.are_equal_ty_list(asdf_ty_dom, nil_tys));

    //let asdf_ty_cod: type_system::Ty = ts.codomain(asdf_ty).unwrap();
    //let string: type_system::Ty = ts.string_ty().unwrap();
    //assert!(ts.are_equal_ty(asdf_ty_cod, string));

    //let void_func: type_system::Expr = ts
    //    .variable_expr(*bindings.get("void_func").unwrap())
    //    .unwrap();
    //let void_func_ty: type_system::Ty = ts.expr_ty(void_func).unwrap();

    //let void_func_ty_cod: type_system::Ty = ts.codomain(void_func_ty).unwrap();
    //let void_ty: type_system::Ty = ts.void_ty().unwrap();
    //assert!(ts.are_equal_ty(void_func_ty_cod, void_ty));

    ExitCode::SUCCESS
}
