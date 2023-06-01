use crate::program::*;

use std::collections::HashMap;

pub struct Literals {
    pub vars: HashMap<String, Var>,
    pub strings: HashMap<String, StringLiteral>,
    pub numbers: HashMap<String, NumberLiteral>,
}

impl Literals {
    pub fn new() -> Literals {
        Literals {
            vars: HashMap::new(),
            strings: HashMap::new(),
            numbers: HashMap::new(),
        }
    }
}

pub fn expr_node_list(nodes: &[ExprNode], p: &mut Program) -> ExprNodeList {
    let mut l = p.new_expr_node_list();
    p.insert_nil_expr_node_list(l);
    for node in nodes.iter().rev() {
        l = p.define_cons_expr_node_list(*node, l);
    }
    l
}

pub fn stmt_node_list(nodes: &[StmtNode], p: &mut Program) -> StmtNodeList {
    let mut l = p.new_stmt_node_list();
    p.insert_nil_stmt_node_list(l);
    for node in nodes.iter().rev() {
        l = p.define_cons_stmt_node_list(*node, l);
    }
    l
}

pub fn type_node_opt(node: Option<TypeNode>, p: &mut Program) -> TypeNodeOpt {
    match node {
        Some(node) => p.define_some_type_node_opt(node),
        None => {
            let tno = p.new_type_node_opt();
            p.insert_none_type_node_opt(tno);
            tno
        }
    }
}

pub fn arg_list(args: &[(Var, TypeNodeOpt)], p: &mut Program) -> ArgList {
    let mut l = p.new_arg_list();
    p.insert_nil_arg_list(l);
    for (var, ty) in args.iter().rev() {
        l = p.define_cons_arg_list(*var, *ty, l);
    }
    l
}
