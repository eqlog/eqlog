use std::collections::BTreeMap;

use eqlog_eqlog::*;
use crate::ast::*;
use crate::semantics::*;

fn encode_rule(rule: &RuleDecl, eqlog: &mut Eqlog, symbols: &BTreeMap<&str, EqlogSymbol>) -> RuleNode {
    let mut eqlog_stmts = eqlog.new_stmt_list_node();
    eqlog.insert_nil_stmt_list_node(eqlog_stmts);

    for stmt in rule.body.iter().rev() {
        let eqlog_stmt = encode_stmt(stmt, eqlog, symbols);
        let cons_eqlog_stmts = eqlog.new_stmt_list_node();
        eqlog.insert_cons_stmt_list_node(cons_eqlog_stmts, eqlog_stmt, eqlog_stmts);
        eqlog_stmts = cons_eqlog_stmts;
    }

    let eqlog_rule = eqlog.new_rule_node();
    eqlog.insert_rule_node_stmts(eqlog_rule, eqlog_stmts);
    eqlog_rule
}

fn encode_stmt(stmt: &Stmt, eqlog: &mut Eqlog, symbols: &BTreeMap<&str, EqlogSymbol>) -> StmtNode {
    let eqlog_stmt = eqlog.new_stmt_node();
    match &stmt.data {
        StmtData::If(atom) => {
            let atom = encode_if_atom(atom, eqlog, symbols);
            eqlog.insert_if_stmt_node(eqlog_stmt, atom);
        }
        StmtData::Then(atom) => {
            let atom = encode_then_atom(atom, eqlog, symbols);
            eqlog.insert_then_stmt_node(eqlog_stmt, atom);
        }
    }
    eqlog_stmt
}

fn encode_if_atom(atom: &IfAtom, eqlog: &mut Eqlog, symbols: &BTreeMap<&str, EqlogSymbol>) -> IfAtomNode {
    match &atom.data {
        IfAtomData::Equal(lhs, rhs) => {
        }
        IfAtomData::Defined(tm) =>  {
        }
        IfAtomData::Pred { pred, args } => todo!(),
        IfAtomData::Var { term, typ } => todo!(),
    }

    todo!()
}

fn encode_then_atom(atom: &ThenAtom, eqlog: &mut Eqlog, symbols: &BTreeMap<&str, EqlogSymbol>) -> ThenAtomNode {
    match &atom.data {
        ThenAtomData::Equal(lhs, rhs) => todo!(),
        ThenAtomData::Defined { var, term } => todo!(),
        ThenAtomData::Pred { pred, args } => todo!(),
    }

    todo!()
}

fn encode_term(term: &Term, eqlog: &mut Eqlog, symbols: &BTreeMap<&str, EqlogSymbol>) -> TermNode {
    todo!()
}
