use convert_case::{Case, Casing};
use eqlog_eqlog::*;
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Display;
use std::iter::successors;

use Case::Snake;

use crate::fmt_util::FmtFn;

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
    eqlog.iter_var().filter_map(move |(strct, el_name, el)| {
        if !eqlog.are_equal_structure(strct, structure) {
            return None;
        }

        let virt_ident = eqlog
            .iter_semantic_name()
            .find_map(|(virt_ident, _, el_name0)| {
                if eqlog.are_equal_el_name(el_name0, el_name) {
                    Some(virt_ident)
                } else {
                    None
                }
            })?;

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

pub fn el_list_vec(mut els: ElList, eqlog: &Eqlog) -> Vec<El> {
    let mut conss = Vec::new();
    let mut snocs = Vec::new();
    loop {
        let cons_entry = eqlog
            .iter_cons_el_list()
            .find(|(_, _, cons_els)| eqlog.are_equal_el_list(*cons_els, els));
        if let Some((head_el, tail_els, _)) = cons_entry {
            conss.push(head_el);
            els = tail_els;
            continue;
        }

        let snoc_entry = eqlog
            .iter_snoc_el_list()
            .find(|(_, _, snoc_els)| eqlog.are_equal_el_list(*snoc_els, els));
        if let Some((init_els, last_el, _)) = snoc_entry {
            snocs.push(last_el);
            els = init_els;
            continue;
        }

        assert!(eqlog
            .iter_nil_el_list()
            .find(|(_, nil)| eqlog.are_equal_el_list(els, *nil))
            .is_some());
        break;
    }

    conss.into_iter().chain(snocs.into_iter().rev()).collect()
}

pub fn type_list_vec(mut types: TypeList, eqlog: &Eqlog) -> Vec<Type> {
    let mut conss = Vec::new();
    let mut snocs = Vec::new();
    loop {
        let cons_entry = eqlog
            .iter_cons_type_list()
            .find(|(_, _, cons_types)| eqlog.are_equal_type_list(*cons_types, types));
        if let Some((head_type, tail_types, _)) = cons_entry {
            conss.push(head_type);
            types = tail_types;
            continue;
        }

        let snoc_entry = eqlog
            .iter_snoc_type_list()
            .find(|(_, _, snoc_types)| eqlog.are_equal_type_list(*snoc_types, types));
        if let Some((init_types, last_type, _)) = snoc_entry {
            snocs.push(last_type);
            types = init_types;
            continue;
        }

        let nil = eqlog
            .nil_type_list()
            .expect("nil_type_list should be defined if there exists a type list");
        assert!(
            eqlog.are_equal_type_list(types, nil),
            "a type_list should be either nil or cons"
        );
        break;
    }

    conss.into_iter().chain(snocs.into_iter().rev()).collect()
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

pub fn el_type(el: El, eqlog: &Eqlog) -> Option<ElementType> {
    eqlog.iter_el_type().find_map(|(e, t)| {
        if eqlog.are_equal_el(e, el) {
            Some(t)
        } else {
            None
        }
    })
}

/// An iterator yielding the natural numbers 0, 1, 2, ... for as long as there is an element
/// representing the natural number in the provided eqlog model.
fn nats<'a>(eqlog: &'a Eqlog) -> impl 'a + Iterator<Item = Nat> {
    successors(eqlog.zero(), move |n| eqlog.succ(*n))
}

pub fn nat(n: Nat, eqlog: &Eqlog) -> usize {
    nats(eqlog)
        .enumerate()
        .find_map(move |(k, n0)| eqlog.are_equal_nat(n0, n).then_some(k))
        .unwrap()
}

struct StructureDisplay<'a> {
    structure: Structure,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
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

pub fn display_type<'a>(
    typ: Type,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let semantic_type_ident = eqlog
            .iter_semantic_type()
            .find_map(|(_sym_scope, ident, typ0)| eqlog.are_equal_type(typ0, typ).then_some(ident));
        if let Some(semantic_type_ident) = semantic_type_ident {
            write!(
                f,
                "{}",
                identifiers.get(&semantic_type_ident).unwrap().as_str()
            )?;
            return Ok(());
        }

        let model_type = eqlog
            .iter_mor_type()
            .find_map(|(model_type, mor_type)| {
                if eqlog.are_equal_type(mor_type, typ) {
                    Some(model_type)
                } else {
                    None
                }
            })
            .expect("Every Type should be either a semantic_type or a mor_type");

        let model_type_ident = eqlog
            .iter_semantic_type()
            .find_map(|(_sym_scope, ident, typ0)| {
                eqlog.are_equal_type(typ0, model_type).then_some(ident)
            })
            .expect("Every model type should be a semantic_type");

        write!(
            f,
            "{}Mor",
            identifiers.get(&model_type_ident).unwrap().as_str()
        )?;
        Ok(())
    })
}

pub fn display_rel<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> String {
    let pred = eqlog.iter_pred_rel().find_map(|(pred, rel0)| {
        if eqlog.are_equal_rel(rel0, rel) {
            Some(pred)
        } else {
            None
        }
    });
    if let Some(pred) = pred {
        let ident = eqlog
            .iter_semantic_pred()
            .find_map(|(_scope, ident, pred0)| eqlog.are_equal_pred(pred0, pred).then_some(ident))
            .expect("Every predicate should be a semantic predicate");
        return identifiers.get(&ident).unwrap().clone();
    }

    let func = eqlog.iter_func_rel().find_map(|(func, rel0)| {
        if eqlog.are_equal_rel(rel0, rel) {
            Some(func)
        } else {
            None
        }
    });

    if let Some(func) = func {
        let semantic_func_ident = eqlog
            .iter_semantic_func()
            .find_map(|(_, ident, func0)| eqlog.are_equal_func(func0, func).then_some(ident));
        if let Some(semantic_func_ident) = semantic_func_ident {
            return identifiers.get(&semantic_func_ident).unwrap().clone();
        }

        let nested_type = eqlog
            .iter_parent_model_func()
            .find_map(|(nested_type, func0)| {
                if eqlog.are_equal_func(func, func0) {
                    Some(nested_type)
                } else {
                    None
                }
            });
        if let Some(nested_type) = nested_type {
            let type_name = display_type(nested_type, eqlog, identifiers)
                .to_string()
                .to_case(Snake);
            return format!("{type_name}_parent");
        }

        let domain_for_mor_type: Option<Type> =
            eqlog
                .iter_mor_type_dom_func()
                .find_map(|(mor_type, func0)| {
                    if eqlog.are_equal_func(func0, func) {
                        Some(mor_type)
                    } else {
                        None
                    }
                });
        let codomain_for_mor_type: Option<Type> =
            eqlog
                .iter_mor_type_cod_func()
                .find_map(|(mor_type, func0)| {
                    if eqlog.are_equal_func(func0, func) {
                        Some(mor_type)
                    } else {
                        None
                    }
                });

        let (mor_type, func_str): (Type, &str) = match (domain_for_mor_type, codomain_for_mor_type)
        {
            (Some(_), Some(_)) => {
                panic!(
                    "Func should be only one of domain or codomain func for a mor type, not both"
                )
            }
            (Some(mor_type), None) => (mor_type, "dom"),
            (None, Some(mor_type)) => (mor_type, "cod"),
            (None, None) => {
                panic!(
                    "Func should be either a domain or codomain func for a mor type, not neither"
                )
            }
        };

        let mor_type = display_type(mor_type, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        return format!("{mor_type}_{func_str}");
    }

    panic!("Rel should be either pred or func")
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

        writeln!(f, "Relations:")?;
        for (rel, args) in eqlog.iter_rel_app() {
            let structure0 = eqlog.els_structure(args).unwrap();
            if !eqlog.are_equal_structure(structure0, *structure) {
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
    }
}

#[allow(unused)]
pub fn display_structure<'a>(
    structure: Structure,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    StructureDisplay {
        structure,
        eqlog,
        identifiers,
    }
}

/// A breadth-first traversal of the morphisms of a rule.
pub fn iter_rule_morphisms<'a>(
    rule: RuleDeclNode,
    eqlog: &'a Eqlog,
) -> impl 'a + Iterator<Item = Vec<Morphism>> {
    let first_dom = eqlog.before_rule_structure(rule).unwrap();

    let first_morphisms: Vec<Morphism> = eqlog
        .iter_dom()
        .filter_map(|(morph, dom)| {
            if eqlog.are_equal_structure(dom, first_dom) {
                Some(morph)
            } else {
                None
            }
        })
        .collect();

    successors(
        (!first_morphisms.is_empty()).then_some(first_morphisms),
        |prev_morphisms| {
            let prev_cods: BTreeSet<Structure> = prev_morphisms
                .iter()
                .copied()
                .map(|morph| eqlog.cod(morph).unwrap())
                .collect();

            let next_morphisms: Vec<Morphism> = eqlog
                .iter_dom()
                .filter_map(|(morph, dom)| {
                    if prev_cods.contains(&dom) {
                        Some(morph)
                    } else {
                        None
                    }
                })
                .collect();

            (!next_morphisms.is_empty()).then_some(next_morphisms)
        },
    )
}
