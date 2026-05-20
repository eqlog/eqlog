use convert_case::{Case, Casing};
use eqlog_eqlog::*;
use std::collections::BTreeMap;
use std::fmt::Display;

use Case::Snake;

use crate::fmt_util::FmtFn;

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
        if let Some(member_type) = eqlog
            .iter_model_member_pred()
            .find_map(|(member_type, p)| eqlog.are_equal_pred(p, pred).then_some(member_type))
        {
            {
                let model_type = eqlog
                    .symbol_scope_model(eqlog.type_definition_symbol_scope(member_type).unwrap())
                    .unwrap();
                let model_type = display_type(model_type, eqlog, identifiers)
                    .to_string()
                    .to_case(Snake);
                let member_type = display_type(member_type, eqlog, identifiers)
                    .to_string()
                    .to_case(Snake);
                return format!("{model_type}_member_{member_type}");
            }
        }

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
        if let Some(domain_for_mor_type) = domain_for_mor_type {
            let mor_type = display_type(domain_for_mor_type, eqlog, identifiers)
                .to_string()
                .to_case(Snake);
            return format!("{mor_type}_dom");
        }

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
        if let Some(codomain_for_mor_type) = codomain_for_mor_type {
            let mor_type = display_type(codomain_for_mor_type, eqlog, identifiers)
                .to_string()
                .to_case(Snake);
            return format!("{mor_type}_cod");
        }

        let app_func_member_type: Option<Type> =
            eqlog.iter_mor_app_func().find_map(|(member_type, func0)| {
                if eqlog.are_equal_func(func0, func) {
                    Some(member_type)
                } else {
                    None
                }
            });

        if let Some(app_func_member_type) = app_func_member_type {
            let app_func_member_type = display_type(app_func_member_type, eqlog, identifiers)
                .to_string()
                .to_case(Snake);
            return format!("{app_func_member_type}_mor_app");
        }

        panic!("Func should be a parent func for a member type, domain or codomain for a type of morphisms or the morphism application func for a member type")
    }

    panic!("Rel should be either pred or func")
}
