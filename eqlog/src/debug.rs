use crate::eqlog_util::*;
use eqlog_eqlog::*;

pub fn display_morphisms(rule: RuleDeclNode, eqlog: &Eqlog) {
    for morphism in iter_rule_morphisms(rule, eqlog) {
        println!("Morphism: {:?}", morphism);
    }
}
