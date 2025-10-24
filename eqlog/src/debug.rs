use crate::eqlog_util::*;
use crate::fmt_util::FmtFn;
use crate::grammar_util::*;
use crate::source_display::SourceDisplay;
use eqlog_eqlog::*;
use itertools::Itertools as _;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Display;

/// Changes the provided `name` so that it corresponds to the lexicographically next name.
fn advance_name(name: &mut Vec<char>, blocked_names: &BTreeSet<Vec<char>>) {
    loop {
        match name.iter().rposition(|c| *c != 'z') {
            Some(last_not_z_index) => {
                let last_not_z = &mut name[last_not_z_index];
                *last_not_z = char::from_u32(u32::from(*last_not_z) + 1).unwrap();
                for c in name[last_not_z_index + 1..].iter_mut() {
                    *c = 'a';
                }
            }
            None => {
                for c in name.iter_mut() {
                    *c = 'a';
                }
                name.push('a');
            }
        }

        if !blocked_names.contains(name) {
            break;
        }
    }
}

fn assign_el_names(
    structure: Structure,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> BTreeMap<El, String> {
    let mut names: BTreeMap<El, String> = iter_vars(structure, eqlog)
        .map(|(ident, el)| {
            let name: String = identifiers.get(&ident).unwrap().to_string();
            (el, name)
        })
        .collect();

    let blocked_names: BTreeSet<Vec<char>> =
        names.values().map(|name| name.chars().collect()).collect();

    let mut current_name = Vec::new();
    for el in iter_els(structure, eqlog) {
        if !names.contains_key(&el) {
            advance_name(&mut current_name, &blocked_names);
            names.insert(el, current_name.iter().copied().collect());
        }
    }
    names
}

fn display_structure<'a>(
    structure: Structure,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let el_names = assign_el_names(structure, eqlog, identifiers);
        writeln!(f, "Elements:")?;
        for (&el, name) in el_names.iter() {
            write!(f, "- {name} {el:?}")?;
            for dep_type in eqlog
                .iter_el_type()
                .filter_map(|(el0, dep_type)| eqlog.are_equal_el(el0, el).then_some(dep_type))
            {
                match eqlog.dep_type_case(dep_type) {
                    DepTypeCase::GlobalType(typ) => {
                        let typ = display_type(typ, eqlog, identifiers);
                        writeln!(f, " of type {typ}")?;
                    }
                    DepTypeCase::MemberType(model_el, typ) => {
                        let typ = display_type(typ, eqlog, identifiers);
                        let model_name = el_names.get(&model_el).unwrap();
                        writeln!(f, " of type {model_name}.{typ}")?;
                    }
                }
            }
            writeln!(f, "")?;
        }

        writeln!(f, "Functions:")?;
        for (func, args, result) in eqlog.iter_func_app() {
            let structure0 = eqlog.els_structure(args).unwrap();
            if !eqlog.are_equal_structure(structure0, structure) {
                continue;
            }
            let structure0 = eqlog.el_structure(result).unwrap();
            assert!(eqlog.are_equal_structure(structure0, structure));

            let args = el_list_vec(args, eqlog)
                .into_iter()
                .map(|arg| el_names.get(&arg).unwrap())
                .format(", ");
            let result = el_names.get(&result).unwrap();

            let rel = eqlog.func_rel(func).unwrap();
            let rel = display_rel(rel, eqlog, identifiers);
            writeln!(f, "- {rel}({args}) = {result}")?;
        }

        writeln!(f, "Relations:")?;
        for (rel, args) in eqlog.iter_rel_app() {
            let structure0 = eqlog.els_structure(args).unwrap();
            if !eqlog.are_equal_structure(structure0, structure) {
                continue;
            }
            let args = el_list_vec(args, eqlog)
                .into_iter()
                .map(|arg| el_names.get(&arg).unwrap())
                .format(", ");
            let rel = display_rel(rel, eqlog, identifiers);
            writeln!(f, "- {rel}({args})")?;
        }

        Ok(())
    })
}

pub fn display_morphisms<'a>(
    rule: RuleDeclNode,
    eqlog: &'a Eqlog,
    locations: &'a BTreeMap<Loc, Location>,
    identifiers: &'a BTreeMap<Ident, String>,
    source: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let mut displayed_structures: BTreeSet<Structure> = BTreeSet::new();
        for morphisms in iter_rule_morphisms(rule, eqlog) {
            for morphism in morphisms {
                let dom = eqlog.dom(morphism).unwrap();
                let cod = eqlog.cod(morphism).unwrap();
                writeln!(f, "{morphism:?}: {dom:?} -> {cod:?}")?;
                for (stmt, morphism0) in eqlog.iter_stmt_morphism() {
                    if !eqlog.are_equal_morphism(morphism, morphism0) {
                        continue;
                    }
                    if let Some(loc) = eqlog.stmt_node_loc(stmt) {
                        let location = *locations
                            .get(&loc)
                            .expect("Every Loc should have a Location");
                        writeln!(f, "{}", SourceDisplay::new(source, location))?;
                    } else {
                        writeln!(f, "Anonymous stmt")?;
                    }
                }

                if !displayed_structures.contains(&dom) {
                    writeln!(
                        f,
                        "{dom:?} =\n{}",
                        display_structure(dom, eqlog, identifiers)
                    )?;
                    displayed_structures.insert(dom);
                }
                if !displayed_structures.contains(&cod) {
                    writeln!(
                        f,
                        "{cod:?} =\n{}",
                        display_structure(cod, eqlog, identifiers)
                    )?;
                    displayed_structures.insert(cod);
                }
            }
        }
        Ok(())
    })
}
