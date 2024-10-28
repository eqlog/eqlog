use eqlog_eqlog::*;
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Display;
use std::iter::{once, successors};

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

//pub fn type_list_vec(mut types: TypeList, eqlog: &Eqlog) -> Vec<Type> {
//    let mut result = Vec::new();
//    loop {
//        let cons_entry = eqlog
//            .iter_cons_type_list()
//            .find(|(_, _, cons_types)| eqlog.are_equal_type_list(*cons_types, types));
//        if let Some((head_type, tail_types, _)) = cons_entry {
//            result.push(head_type);
//            types = tail_types;
//            continue;
//        }
//
//        let nil = eqlog
//            .nil_type_list()
//            .expect("nil_type_list should be defined if there exists a type list");
//        assert!(
//            eqlog.are_equal_type_list(types, nil),
//            "a type_list should be either nil or cons"
//        );
//        break;
//    }
//
//    result
//}
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

pub fn el_type(el: El, eqlog: &Eqlog) -> Option<Type> {
    eqlog.iter_el_type().find_map(|(e, t)| {
        if eqlog.are_equal_el(e, el) {
            Some(t)
        } else {
            None
        }
    })
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

pub fn semantic_type_ident(ty: Type, eqlog: &Eqlog) -> Ident {
    eqlog
        .iter_semantic_type()
        .find_map(|(_, ident, ty0)| eqlog.are_equal_type(ty0, ty).then_some(ident))
        .unwrap()
}

pub fn iter_func_arities<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Iterator<Item = (&'a str, Vec<&'a str>)> {
    eqlog.iter_semantic_func().map(|(_, ident, func)| {
        let name = identifiers.get(&ident).unwrap().as_str();
        let domain_tys: Vec<Type> = type_list_vec(eqlog.domain(func).unwrap(), eqlog);
        let codomain: Type = eqlog.codomain(func).unwrap();

        let arity: Vec<&str> = domain_tys
            .into_iter()
            .chain(once(codomain))
            .map(|ty| {
                let ident = semantic_type_ident(ty, eqlog);
                identifiers.get(&ident).unwrap().as_str()
            })
            .collect();

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

pub fn display_rel<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
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
            .expect("semantic_pred should be surjective");
        return identifiers.get(&ident).unwrap().as_str();
    }

    let func = eqlog.iter_func_rel().find_map(|(func, rel0)| {
        if eqlog.are_equal_rel(rel0, rel) {
            Some(func)
        } else {
            None
        }
    });
    if let Some(func) = func {
        let ident = eqlog
            .iter_semantic_func()
            .find_map(|(_, ident, func0)| eqlog.are_equal_func(func0, func).then_some(ident))
            .expect("semantic_func should be surjective");
        return identifiers.get(&ident).unwrap().as_str();
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

pub fn iter_symbol_scope_types<'a>(
    symbol_scope: SymbolScope,
    eqlog: &'a Eqlog,
) -> impl 'a + Iterator<Item = Type> {
    let type_kind = eqlog.type_symbol().unwrap();
    let enum_kind = eqlog.enum_symbol().unwrap();
    let model_kind = eqlog.model_symbol().unwrap();
    eqlog
        .iter_defined_symbol()
        .filter_map(move |(sym_scope0, name, sym_kind, _loc)| {
            (sym_scope0 == symbol_scope).then_some(())?;
            (eqlog.are_equal_symbol_kind(sym_kind, type_kind)
                || eqlog.are_equal_symbol_kind(sym_kind, enum_kind)
                || eqlog.are_equal_symbol_kind(sym_kind, model_kind))
            .then_some(())?;
            Some(eqlog.semantic_type(symbol_scope, name).unwrap())
        })
}

pub fn iter_symbol_scope_relations<'a>(
    symbol_scope: SymbolScope,
    eqlog: &'a Eqlog,
) -> impl 'a + Iterator<Item = Rel> {
    let pred_kind = eqlog.pred_symbol().unwrap();
    let func_kind = eqlog.func_symbol().unwrap();
    let ctor_kind = eqlog.ctor_symbol().unwrap();
    eqlog
        .iter_defined_symbol()
        .filter_map(move |(sym_scope0, name, sym_kind, _loc)| {
            (sym_scope0 == symbol_scope).then_some(())?;
            if eqlog.are_equal_symbol_kind(sym_kind, pred_kind) {
                let pred = eqlog.semantic_pred(symbol_scope, name).unwrap();
                return Some(eqlog.pred_rel(pred).unwrap());
            }

            if eqlog.are_equal_symbol_kind(sym_kind, func_kind)
                || eqlog.are_equal_symbol_kind(sym_kind, ctor_kind)
            {
                let func = eqlog.semantic_func(symbol_scope, name).unwrap();
                return Some(eqlog.func_rel(func).unwrap());
            }

            None
        })
}
