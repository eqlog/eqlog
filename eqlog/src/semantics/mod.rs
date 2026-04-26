use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::iter;

use itertools::Itertools;

use crate::eqlog_util::*;
use crate::error::*;
use crate::grammar_util::*;
use eqlog_eqlog::*;

fn element_type_to_string<'a>(
    typ: DepType,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    _locations: &'a BTreeMap<Loc, Location>,
) -> String {
    match eqlog.dep_type_case(typ) {
        DepTypeCase::GlobalType(typ) => display_type(typ, eqlog, identifiers).to_string(),
        DepTypeCase::MemberType(el, typ) => {
            let typ = display_type(typ, eqlog, identifiers).to_string();

            let name = match eqlog
                .iter_var()
                .find_map(|(_, name, el0)| eqlog.are_equal_el(el0, el).then_some(name))
            {
                Some(name) => name,
                None => {
                    // TODO: Do better here. This happens if the model element is not given by a
                    // variable but by a composed term.
                    return format!("?.{typ}");
                }
            };

            let virt_ident = eqlog
                .iter_semantic_name()
                .find_map(|(virt_ident, _scope, name0)| {
                    eqlog.are_equal_el_name(name0, name).then_some(virt_ident)
                })
                .expect(
                    "Every semantic name should be given by a virtual identifier in some scope",
                );

            let ident = match eqlog.virt_real_ident(virt_ident) {
                Some(ident) => ident,
                None => {
                    // The variable is a wildcard.
                    return format!("_.{typ}");
                }
            };
            let s = identifiers.get(&ident).unwrap();

            return format!("{s}.{typ}");
        }
    }
}

pub fn iter_conflicting_type_errors<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    let mut el_types: BTreeMap<El, Vec<DepType>> = BTreeMap::new();
    for (el, ty) in eqlog.iter_el_type() {
        let tys = el_types.entry(el).or_default();
        if !tys.contains(&ty) {
            tys.push(ty);
        }
    }

    el_types
        .into_iter()
        .filter(|(_, tys)| tys.len() > 1)
        .flat_map(move |(el, tys)| {
            let types: Vec<String> = tys
                .into_iter()
                .map(|ty| element_type_to_string(ty, eqlog, identifiers, locations))
                .collect();
            eqlog.iter_semantic_el().filter_map(move |(tm, _, e)| {
                if !eqlog.are_equal_el(e, el) {
                    return None;
                }

                let loc = eqlog.term_node_loc(tm).unwrap();
                let location = *locations.get(&loc).unwrap();

                Some(CompileError::ConflictingTermType {
                    types: types.clone(),
                    location,
                })
            })
        })
}

pub fn iter_undetermined_type_errors<'a>(
    eqlog: &'a Eqlog,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    let all_els: BTreeSet<El> = eqlog.iter_el().collect();
    let els_with_type: BTreeSet<El> = eqlog.iter_el_type().map(|(el, _)| el).collect();

    all_els
        .into_iter()
        .filter(move |el| !els_with_type.contains(el))
        .flat_map(move |el| {
            eqlog.iter_semantic_el().filter_map(move |(tm, _, e)| {
                if !eqlog.are_equal_el(e, el) {
                    return None;
                }

                let loc = eqlog.term_node_loc(tm)?;
                let location = *locations.get(&loc).unwrap();
                return Some(CompileError::UndeterminedTermType { location });
            })
        })
}

pub fn iter_symbol_lookup_errors<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    // In case of multiple declared of a symbol, symbol lookup should go through if at least on
    // declaration is of the right kind. Since the SymbolDeclaredTwice error is probably the root
    // cause, it should be reported with higher preference.
    let mut declared_symbols: BTreeMap<(SymbolScope, Ident), Vec<(SymbolKind, Location)>> =
        BTreeMap::new();
    for (scope, name, kind, loc) in eqlog.iter_accessible_symbol() {
        let location = *locations.get(&loc).unwrap();
        declared_symbols
            .entry((scope, name))
            .or_insert(Vec::new())
            .push((kind, location));
    }
    for decls in declared_symbols.values_mut() {
        decls.sort_by_key(|(_, location)| location.1);
    }

    eqlog
        .iter_should_be_symbol()
        .map(|(ident, kind, scope, loc)| (ident, vec![kind], scope, loc))
        .chain(
            eqlog
                .iter_should_be_symbol_2()
                .map(|(ident, kind1, kind2, scope, loc)| (ident, vec![kind1, kind2], scope, loc)),
        )
        .chain(
            eqlog
                .iter_should_be_symbol_3()
                .map(|(ident, kind1, kind2, kind3, scope, loc)| {
                    (ident, vec![kind1, kind2, kind3], scope, loc)
                }),
        )
        .filter_map(move |(ident, expected_kinds, scope, loc)| {
            let name: &str = identifiers.get(&ident).unwrap().as_str();
            let location = *locations.get(&loc).unwrap();

            let decls: &[(SymbolKind, Location)] = match declared_symbols.get(&(scope, ident)) {
                None => {
                    return Some(CompileError::UndeclaredSymbol {
                        name: name.to_string(),
                        used_at: location,
                    });
                }
                Some(decls) => decls.as_slice(),
            };

            // This is the primary kind of symbol we show in the error message, e.g. "function"
            // instead of "function or constructor".
            let primary_expected_kind = expected_kinds[0];

            match decls
                .iter()
                .cartesian_product(expected_kinds.iter())
                .find(|((decl_kind, _), expected_kind)| decl_kind == *expected_kind)
            {
                Some(_) => None,
                None => {
                    let (decl_kind, decl_location) = decls[0];
                    Some(CompileError::BadSymbolKind {
                        name: name.to_string(),
                        expected: eqlog.symbol_kind_case(primary_expected_kind),
                        found: eqlog.symbol_kind_case(decl_kind),
                        used_at: location,
                        declared_at: decl_location,
                    })
                }
            }
        })
}

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
        .chain(iter_symbol_lookup_errors(eqlog, identifiers, locations))
        .chain(iter_conflicting_type_errors(eqlog, identifiers, locations))
        .chain(iter_undetermined_type_errors(eqlog, locations))
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
