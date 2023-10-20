use std::cmp::{max, min};
use std::collections::BTreeMap;

use eqlog_eqlog::*;

// TODO: Use rust's built-in never type ! once it is stabilized.
pub enum NeverType {}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Location(pub usize, pub usize);

impl Location {
    pub fn is_empty(self) -> bool {
        self.0 == self.1
    }
    pub fn intersect(self, other: Self) -> Option<Self> {
        let begin = max(self.0, other.0);
        let end = min(self.1, other.1);
        if !self.is_empty() && !other.is_empty() {
            // For non-empty locations, we only consider non-empty intersections.
            if begin < end {
                Some(Location(begin, end))
            } else {
                None
            }
        } else {
            debug_assert!(self.is_empty() || other.is_empty());
            // We return a valid location also in cases where an empty location points to right
            // before or right after a non-empty location.
            if begin <= end {
                Some(Location(begin, end))
            } else {
                None
            }
        }
    }
}

pub fn make_loc(
    location: Location,
    eqlog: &mut Eqlog,
    locations: &mut BTreeMap<Location, Loc>,
) -> Loc {
    *locations.entry(location).or_insert_with(|| eqlog.new_loc())
}

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
