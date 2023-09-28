use eqlog_eqlog::*;

// TODO: Use rust's built-in never type ! once it is stabilized.
pub enum NeverType {}

pub fn term_list_node(nodes: &[TermNode], eqlog: &mut Eqlog) -> TermListNode {
    let mut l = eqlog.new_term_list_node();
    eqlog.insert_nil_term_list_node(l);
    for node in nodes.iter().rev() {
        let cons = eqlog.new_term_list_node();
        eqlog.insert_cons_term_list_node(cons, *node, l);
        l = cons;
    }
    l
}

pub fn stmt_list_node(nodes: &[StmtNode], eqlog: &mut Eqlog) -> StmtListNode {
    let mut l = eqlog.new_stmt_list_node();
    eqlog.insert_nil_stmt_list_node(l);
    for node in nodes.iter().rev() {
        let cons = eqlog.new_stmt_list_node();
        eqlog.insert_cons_stmt_list_node(cons, *node, l);
        l = cons;
    }
    l
}

pub fn decl_list_node(nodes: &[DeclNode], eqlog: &mut Eqlog) -> DeclListNode {
    let mut l = eqlog.new_decl_list_node();
    eqlog.insert_nil_decl_list_node(l);
    for node in nodes.iter().rev() {
        let cons = eqlog.new_decl_list_node();
        eqlog.insert_cons_decl_list_node(cons, *node, l);
        l = cons;
    }
    l
}

pub fn arg_decl_list_node(nodes: &[ArgDeclNode], eqlog: &mut Eqlog) -> ArgDeclListNode {
    let mut l = eqlog.new_arg_decl_list_node();
    eqlog.insert_nil_arg_decl_list_node(l);
    for node in nodes.iter().rev() {
        let cons = eqlog.new_arg_decl_list_node();
        eqlog.insert_cons_arg_decl_list_node(cons, *node, l);
        l = cons;
    }
    l
}

pub fn opt_term_node(o: Option<TermNode>, eqlog: &mut Eqlog) -> OptTermNode {
    let opt_node = eqlog.new_opt_term_node();
    match o {
        Some(n) => {
            eqlog.insert_some_term_node(opt_node, n);
        }
        None => {
            eqlog.insert_none_term_node(opt_node);
        }
    }
    opt_node
}
