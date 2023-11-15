use crate::error::SymbolKindEnum;
use eqlog_eqlog::*;
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Display;
use std::iter::successors;

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

pub fn type_list_vec(mut types: TypeList, eqlog: &Eqlog) -> Vec<Type> {
    let mut result = Vec::new();
    loop {
        let cons_entry = eqlog
            .iter_cons_type_list()
            .find(|(_, _, cons_types)| eqlog.are_equal_type_list(*cons_types, types));
        if let Some((head_type, tail_types, _)) = cons_entry {
            result.push(head_type);
            types = tail_types;
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

pub fn el_type(el: El, eqlog: &Eqlog) -> Option<Type> {
    eqlog.iter_el_type().find_map(|(e, t)| {
        if eqlog.are_equal_el(e, el) {
            Some(t)
        } else {
            None
        }
    })
}

pub fn symbol_kind(kind: SymbolKind, eqlog: &Eqlog) -> SymbolKindEnum {
    if eqlog.are_equal_symbol_kind(kind, eqlog.type_symbol().unwrap()) {
        return SymbolKindEnum::Type;
    }
    if eqlog.are_equal_symbol_kind(kind, eqlog.pred_symbol().unwrap()) {
        return SymbolKindEnum::Pred;
    }
    if eqlog.are_equal_symbol_kind(kind, eqlog.func_symbol().unwrap()) {
        return SymbolKindEnum::Func;
    }
    if eqlog.are_equal_symbol_kind(kind, eqlog.rule_symbol().unwrap()) {
        return SymbolKindEnum::Rule;
    }

    panic!("Invalid symbol kind")
}

pub fn arg_decl_types<'a>(
    mut arg_decls: ArgDeclListNode,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> Vec<&'a str> {
    let mut result = Vec::new();
    loop {
        if eqlog.nil_arg_decl_list_node(arg_decls) {
            break;
        }

        let (head_arg_decl, tail_arg_decls) = eqlog
            .iter_cons_arg_decl_list_node()
            .find_map(|(args0, head, tail)| {
                eqlog
                    .are_equal_arg_decl_list_node(args0, arg_decls)
                    .then_some((head, tail))
            })
            .expect("ArgDeclListNode should be either nil or cons");

        let head_ident = eqlog
            .iter_arg_decl_node_type()
            .find_map(|(arg_decl, ident)| {
                eqlog
                    .are_equal_arg_decl_node(arg_decl, head_arg_decl)
                    .then_some(ident)
            })
            .expect("ArgDeclNode should have a type");

        let head_name = identifiers.get(&head_ident).unwrap().as_str();

        result.push(head_name);
        arg_decls = tail_arg_decls;
    }

    result
}

pub fn iter_pred_arities<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Iterator<Item = (&'a str, Vec<&'a str>)> {
    eqlog.iter_pred_decl().map(|(_, ident, arg_decls)| {
        let name = identifiers.get(&ident).unwrap().as_str();
        let arity = arg_decl_types(arg_decls, eqlog, identifiers);
        (name, arity)
    })
}

pub fn iter_func_arities<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Iterator<Item = (&'a str, Vec<&'a str>)> {
    eqlog
        .iter_func_decl()
        .map(|(_, ident, arg_decls, result_ident)| {
            let name = identifiers.get(&ident).unwrap().as_str();
            let mut arity = arg_decl_types(arg_decls, eqlog, identifiers);
            arity.push(identifiers.get(&result_ident).unwrap().as_str());
            (name, arity)
        })
}

pub fn iter_relation_arities<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Iterator<Item = (&'a str, Vec<&'a str>)> {
    iter_pred_arities(eqlog, identifiers).chain(iter_func_arities(eqlog, identifiers))
}

pub fn get_arity<'a>(
    rel: &'a str,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> Option<Vec<&'a str>> {
    iter_relation_arities(eqlog, identifiers).find_map(|(r, arity)| (r == rel).then_some(arity))
}

pub fn iter_types<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Iterator<Item = &'a str> {
    eqlog
        .iter_type_decl()
        .map(|(_, type_ident)| identifiers.get(&type_ident).unwrap().as_str())
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
            let pred_name: &str = identifiers.get(&pred_ident).unwrap().as_str();
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
            let func_name: &str = identifiers.get(&func_ident).unwrap().as_str();
            writeln!(f, "- {func_name}({args}) = {result}")?;
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
