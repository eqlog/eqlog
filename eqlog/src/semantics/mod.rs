use std::collections::BTreeMap;
use std::iter;

use itertools::Itertools;

use crate::error::*;
use crate::grammar_util::*;
use eqlog_eqlog::*;

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

pub fn check_eqlog(
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
    locations: &BTreeMap<Loc, Location>,
) -> Result<(), CompileError> {
    let first_error: Option<CompileError> = iter::empty()
        .chain(iter_symbol_lookup_errors(eqlog, identifiers, locations))
        .chain(iter_enum_ctors_not_surjective_errors(
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
