use eqlog_eqlog::*;
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Display;

pub fn iter_els<'a>(structure: Structure, eqlog: &'a Eqlog) -> impl 'a + Iterator<Item = El> {
    eqlog.iter_el_structure().filter_map(move |(el, strct)| {
        if eqlog.are_equal_structure(strct, structure) {
            Some(el)
        } else {
            None
        }
    })
}

pub fn iter_vars<'a>(
    structure: Structure,
    eqlog: &'a Eqlog,
) -> impl 'a + Iterator<Item = (Ident, El)> {
    eqlog.iter_var().filter_map(move |(strct, virt_ident, el)| {
        if !eqlog.are_equal_structure(strct, structure) {
            return None;
        }
        let ident = eqlog.iter_real_virt_ident().find_map(|(ident, vrt_id)| {
            if eqlog.are_equal_virt_ident(vrt_id, virt_ident) {
                Some(ident)
            } else {
                None
            }
        })?;

        Some((ident, el))
    })
}

pub fn iter_pred_app<'a>(
    structure: Structure,
    eqlog: &'a Eqlog,
) -> impl 'a + Iterator<Item = (Pred, ElList)> {
    eqlog.iter_pred_app().filter_map(move |(pred, args)| {
        if !eqlog.are_equal_structure(eqlog.els_structure(args).unwrap(), structure) {
            return None;
        }

        Some((pred, args))
    })
}

pub fn iter_func_app<'a>(
    structure: Structure,
    eqlog: &'a Eqlog,
) -> impl 'a + Iterator<Item = (Func, ElList, El)> {
    eqlog
        .iter_func_app()
        .filter_map(move |(func, args, result)| {
            if !eqlog.are_equal_structure(eqlog.els_structure(args).unwrap(), structure) {
                return None;
            }
            assert!(eqlog.are_equal_structure(eqlog.el_structure(result).unwrap(), structure));

            Some((func, args, result))
        })
}

pub fn el_list_vec(mut els: ElList, eqlog: &Eqlog) -> Vec<El> {
    let mut result = Vec::new();
    loop {
        let cons_entry = eqlog
            .iter_cons_el_list()
            .find(|(_, _, cons_els)| eqlog.are_equal_el_list(*cons_els, els));
        if let Some((head_el, tail_els, _)) = cons_entry {
            result.push(head_el);
            els = tail_els;
            continue;
        }

        assert!(eqlog
            .iter_nil_el_list()
            .find(|(_, nil)| eqlog.are_equal_el_list(els, *nil))
            .is_some());
        break;
    }

    result
}

pub fn iter_in_ker<'a>(
    morphism: Morphism,
    eqlog: &'a Eqlog,
) -> impl 'a + Iterator<Item = (El, El)> {
    eqlog.iter_in_ker().filter_map(move |(morph, el0, el1)| {
        if !eqlog.are_equal_morphism(morphism, morph) {
            return None;
        }

        Some((el0, el1))
    })
}

struct StructureDisplay<'a> {
    structure: Structure,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<String, Ident>,
}

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
    identifiers: &BTreeMap<String, Ident>,
) -> BTreeMap<El, String> {
    let mut names: BTreeMap<El, String> = iter_vars(structure, eqlog)
        .map(|(ident, el)| {
            let name = identifiers
                .iter()
                .find_map(|(name, id)| eqlog.are_equal_ident(*id, ident).then_some(name.as_str()))
                .unwrap();
            (el, name.to_string())
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

impl<'a> Display for StructureDisplay<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let Self {
            structure,
            eqlog,
            identifiers,
        } = self;

        let el_names = assign_el_names(*structure, eqlog, *identifiers);
        writeln!(f, "Elements:")?;
        for name in el_names.values() {
            writeln!(f, "- {name}")?;
        }

        writeln!(f, "Predicates:")?;
        for (pred, args) in iter_pred_app(*structure, eqlog) {
            let args = el_list_vec(args, eqlog)
                .into_iter()
                .map(|arg| el_names.get(&arg).unwrap())
                .format(", ");
            let pred_ident = eqlog
                .iter_semantic_pred()
                .find_map(|(ident, prd)| eqlog.are_equal_pred(prd, pred).then_some(ident))
                .unwrap();
            let pred_name = identifiers
                .iter()
                .find_map(|(name, ident)| {
                    eqlog
                        .are_equal_ident(*ident, pred_ident)
                        .then_some(name.as_str())
                })
                .unwrap();
            writeln!(f, "- {pred_name}({args})")?;
        }

        writeln!(f, "Functions:")?;
        for (func, args, result) in iter_func_app(*structure, eqlog) {
            let args = el_list_vec(args, eqlog)
                .into_iter()
                .map(|arg| el_names.get(&arg).unwrap())
                .format(", ");
            let result = el_names.get(&result).unwrap();

            let func_ident = eqlog
                .iter_semantic_func()
                .find_map(|(ident, fnc)| eqlog.are_equal_func(fnc, func).then_some(ident))
                .unwrap();
            let func_name = identifiers
                .iter()
                .find_map(|(name, ident)| {
                    eqlog
                        .are_equal_ident(*ident, func_ident)
                        .then_some(name.as_str())
                })
                .unwrap();
            writeln!(f, "- {func_name}({args}) = {result}")?;
        }
        Ok(())
    }
}

#[allow(unused)]
pub fn display_structure<'a>(
    structure: Structure,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<String, Ident>,
) -> impl 'a + Display {
    StructureDisplay {
        structure,
        eqlog,
        identifiers,
    }
}
