use crate::program::*;
use std::fmt;
use std::fmt::Display;

#[derive(Copy, Clone, Debug)]
pub struct Indent(pub usize);

impl Indent {
    pub fn new() -> Indent {
        Indent(0)
    }
    pub fn more(self) -> Indent {
        Indent(self.0 + 1)
    }
    pub fn less(self) -> Option<Indent> {
        if self.0 > 0 {
            Some(Indent(self.0 - 1))
        } else {
            None
        }
    }
}

impl Display for Indent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for _ in 0..self.0 {
            write!(f, "  ")?;
        }
        Ok(())
    }
}

pub fn type_node_opt(tno: TypeNodeOpt, p: &Program) -> Option<TypeNode> {
    if p.none_type_node_opt(tno) {
        return None;
    }
    if let Some((tn, _)) = p
        .iter_some_type_node_opt()
        .find(|(_, some_tno)| *some_tno == tno)
    {
        return Some(tn);
    }

    panic!("TypeNodeOpt is neither None nor Some: {tno}");
}

pub fn arg_list(mut arg_list: ArgList, p: &Program) -> Vec<(Var, Option<TypeNode>)> {
    let mut result = Vec::new();
    while !p.nil_arg_list(arg_list) {
        let (head_var, head_tno, tail, _) = p
            .iter_cons_arg_list()
            .find(|(_, _, _, result)| *result == arg_list)
            .unwrap(); //"Arg list is neither nil nor cons"
        result.push((head_var, type_node_opt(head_tno, p)));
        arg_list = tail;
    }

    result
}

pub fn type_list(mut ts: TypeList, p: &Program) -> Vec<Type> {
    let mut result = Vec::new();
    while p.nil_type_list() != Some(ts) {
        let (head, tail, _) = p
            .iter_cons_type_list()
            .find(|(_, _, result)| *result == ts)
            .unwrap(); //"Arg list is neither nil nor cons"
        result.push(head);
        ts = tail;
    }

    result
}

pub fn print_type_node(tn: TypeNode, p: &Program, indent: Indent) {
    let tn0 = tn.0;
    if p.void_type_node(tn) {
        println!("{indent}- VoidTypeNode({tn0})");
        return;
    }
    if p.boolean_type_node(tn) {
        println!("{indent}- BooleanTypeNode({tn0}");
        return;
    }
    if p.number_type_node(tn) {
        println!("{indent}- NumberTypeNode({tn0})");
        return;
    }
    if p.string_type_node(tn) {
        println!("{indent}- StringTypeNode({tn0})");
        return;
    }

    if let Some((_, args, codomain)) = p
        .iter_function_type_node()
        .find(|(func_tn, _, _)| *func_tn == tn)
    {
        println!("{indent}- FunctionTypeNode({tn0})");
        let indent1 = indent.more();
        let indent2 = indent1.more();
        println!("{indent1}- Domain");
        for (_, opt_type_node) in arg_list(args, p) {
            match opt_type_node {
                None => println!("{indent2}- <None>"),
                Some(tn) => print_type_node(tn, p, indent2),
            }
        }
        println!("{indent1}- Codomain");
        print_type_node(codomain, p, indent2);
        return;
    }

    panic!("Invalid type node: {tn}");
}

pub fn print_type(t: Type, p: &Program, indent: Indent) {
    let t0 = t.0;
    if p.void_type() == Some(t) {
        println!("{indent}- VoidType({t0})");
        return;
    }
    if p.boolean_type() == Some(t) {
        println!("{indent}- BooleanType({t0}");
        return;
    }
    if p.number_type() == Some(t) {
        println!("{indent}- NumberType({t0})");
        return;
    }
    if p.string_type() == Some(t) {
        println!("{indent}- StringType({t0})");
        return;
    }

    if let Some((domain, codomain, _)) = p.iter_function_type().find(|(_, _, func)| *func == t) {
        let domain = type_list(domain, p);
        println!("{indent}- FunctionType({t0})");
        let indent1 = indent.more();
        let indent2 = indent1.more();
        println!("{indent1}- Domain");
        for d in domain {
            print_type(d, p, indent2);
        }
        println!("{indent1}- Codomain");
        print_type(codomain, p, indent2);
        return;
    }

    println!("{indent}- Type({t0})");
}

pub fn var_type(var: Var, p: &Program) -> Type {
    let mut vts = p
        .iter_var_type_in_stmts()
        .filter(|(var0, _, _)| *var0 == var);
    let ty = match vts.next() {
        Some((_, _, ty)) => ty,
        None => panic!("Variable not found"),
    };

    for (_, _, ty0) in vts {
        assert!(p.are_equal_type(ty, ty0), "Variable type not unique");
    }

    ty
}
