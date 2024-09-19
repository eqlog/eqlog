use crate::eqlog_util::*;
use crate::grammar_util::*;
use crate::source_display::SourceDisplay;
use eqlog_eqlog::*;
use std::collections::{BTreeMap, BTreeSet};

pub fn display_morphisms(
    rule: RuleDeclNode,
    eqlog: &Eqlog,
    locations: &BTreeMap<Loc, Location>,
    identifiers: &BTreeMap<Ident, String>,
    source: &str,
) {
    let mut displayed_structures: BTreeSet<Structure> = BTreeSet::new();
    for morphisms in iter_rule_morphisms(rule, eqlog) {
        for morphism in morphisms {
            let dom = eqlog.dom(morphism).unwrap();
            let cod = eqlog.cod(morphism).unwrap();
            println!("{morphism:?}: {dom:?} -> {cod:?}");
            for (stmt, morphism0) in eqlog.iter_stmt_morphism() {
                if !eqlog.are_equal_morphism(morphism, morphism0) {
                    continue;
                }
                if let Some(loc) = eqlog.stmt_node_loc(stmt) {
                    let location = *locations
                        .get(&loc)
                        .expect("Every Loc should have a Location");
                    println!("{}", SourceDisplay::new(source, location));
                } else {
                    println!("Anonymous stmt");
                }
            }

            if !displayed_structures.contains(&dom) {
                println!("{dom:?} =\n{}", display_structure(dom, eqlog, identifiers));
                displayed_structures.insert(dom);
            }
            if !displayed_structures.contains(&cod) {
                println!("{cod:?} =\n{}", display_structure(cod, eqlog, identifiers));
                displayed_structures.insert(cod);
            }
        }
    }
}
