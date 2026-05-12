use std::collections::BTreeMap;
use std::iter;

use crate::error::*;
use crate::grammar_util::*;
use eqlog_eqlog::*;

pub fn iter_enum_ctors_not_surjective_errors<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    eqlog
        .iter_should_be_obtained_by_ctor()
        .filter_map(|(term_node, enum_node)| {
            if eqlog.is_given_by_ctor(term_node, enum_node) {
                return None;
            }

            let term_location = *locations
                .get(&eqlog.term_node_loc(term_node).unwrap())
                .unwrap();
            let enum_location = *locations
                .get(&eqlog.enum_decl_node_loc(enum_node).unwrap())
                .unwrap();
            let enum_name = eqlog
                .iter_enum_decl()
                .find_map(|(enum_node0, ident, _)| {
                    if eqlog.are_equal_enum_decl_node(enum_node, enum_node0) {
                        Some(identifiers.get(&ident).unwrap().to_owned())
                    } else {
                        None
                    }
                })
                .unwrap();

            Some(CompileError::EnumCtorsNotSurjective {
                term_location,
                enum_location,
                enum_name,
            })
        })
}

pub fn iter_non_morphism_applied_as_morphism_errors<'a>(
    eqlog: &'a Eqlog,
    _identifiers: &'a BTreeMap<Ident, String>,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    eqlog.iter_should_be_mor_el().filter_map(|(el, loc)| {
        if !eqlog.is_mor_el(el) {
            let location = *locations.get(&loc).unwrap();
            Some(CompileError::NonMorphismAppliedAsMorphism { location })
        } else {
            None
        }
    })
}

pub fn iter_morphism_applied_to_non_member_errors<'a>(
    eqlog: &'a Eqlog,
    _identifiers: &'a BTreeMap<Ident, String>,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    eqlog
        .iter_should_be_member_element()
        .filter_map(|(el, model_type, loc)| {
            if !eqlog.is_member_element(el, model_type) {
                let location = *locations.get(&loc).unwrap();
                Some(CompileError::MorphismAppliedToNonMember { location })
            } else {
                None
            }
        })
}

pub fn check_eqlog(
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
    locations: &BTreeMap<Loc, Location>,
) -> Result<(), CompileError> {
    let first_error: Option<CompileError> = iter::empty()
        .chain(iter_enum_ctors_not_surjective_errors(
            eqlog,
            identifiers,
            locations,
        ))
        .chain(iter_non_morphism_applied_as_morphism_errors(
            eqlog,
            identifiers,
            locations,
        ))
        .chain(iter_morphism_applied_to_non_member_errors(
            eqlog,
            identifiers,
            locations,
        ))
        .min();

    if let Some(err) = first_error {
        Err(err)
    } else {
        Ok(())
    }
}
