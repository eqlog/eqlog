mod check_epic;

use std::collections::btree_map;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::iter;

use check_epic::*;
use convert_case::Case;
use convert_case::Casing;

use crate::eqlog_util::*;
use crate::error::*;
use crate::grammar_util::*;
use eqlog_eqlog::*;

pub fn iter_variable_not_snake_case_errors<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    eqlog.iter_var_term_node().filter_map(|(tm, ident)| {
        let name: &str = identifiers.get(&ident).unwrap().as_str();

        if name == &name.to_case(Case::Snake) {
            return None;
        }

        let loc = eqlog.term_node_loc(tm).unwrap();
        let location = *locations.get(&loc).unwrap();

        Some(CompileError::VariableNotSnakeCase {
            name: name.to_string(),
            location,
        })
    })
}

pub fn iter_variable_occurs_twice<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    let mut var_tms: BTreeMap<(RuleDeclNode, Ident), BTreeSet<TermNode>> = BTreeMap::new();

    for (tm, ident, rule) in eqlog.iter_var_term_in_rule() {
        var_tms
            .entry((rule, ident))
            .or_insert(BTreeSet::new())
            .insert(tm);
    }

    var_tms.into_iter().filter_map(|((_, ident), var_tms)| {
        if var_tms.len() >= 2 {
            return None;
        }

        assert!(var_tms.len() == 1);
        let var_tm = var_tms.into_iter().next().unwrap();

        let name: &str = identifiers.get(&ident).unwrap().as_str();

        let loc = eqlog.term_node_loc(var_tm).unwrap();
        let location = *locations.get(&loc).unwrap();

        Some(CompileError::VariableOccursOnlyOnce {
            name: name.to_string(),
            location,
        })
    })
}

pub fn iter_conflicting_type_errors<'a>(
    eqlog: &'a Eqlog,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    let mut el_type: BTreeMap<El, Type> = BTreeMap::new();
    eqlog
        .iter_el_type()
        .filter_map(move |(el, ty)| match el_type.entry(el) {
            btree_map::Entry::Vacant(vacant) => {
                vacant.insert(ty);
                None
            }
            btree_map::Entry::Occupied(occupied) => {
                if eqlog.are_equal_type(*occupied.get(), ty) {
                    None
                } else {
                    Some(el)
                }
            }
        })
        .flat_map(move |el| {
            eqlog.iter_semantic_el().filter_map(move |(tm, e)| {
                if !eqlog.are_equal_el(e, el) {
                    return None;
                }

                let loc = eqlog.term_node_loc(tm).unwrap();
                let location = *locations.get(&loc).unwrap();

                Some(CompileError::ConflictingTermType {
                    types: Vec::new(),
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
            eqlog.iter_semantic_el().filter_map(move |(tm, e)| {
                if !eqlog.are_equal_el(e, el) {
                    return None;
                }

                let loc = eqlog.term_node_loc(tm).unwrap();
                let location = *locations.get(&loc).unwrap();
                return Some(CompileError::UndeterminedTermType { location });
            })
        })
}

pub fn iter_if_after_then_errors<'a>(
    eqlog: &'a Eqlog,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    eqlog.iter_if_after_then().map(|if_stmt| {
        let loc = eqlog.stmt_node_loc(if_stmt).unwrap();
        let location = *locations.get(&loc).unwrap();
        CompileError::IfAfterThen { location }
    })
}

pub fn iter_symbol_declared_twice_errors<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    let mut symbols: BTreeMap<Ident, Vec<Loc>> = BTreeMap::new();
    for (name, _, loc) in eqlog.iter_defined_symbol() {
        symbols.entry(name).or_insert(Vec::new()).push(loc);
    }

    symbols.into_iter().filter_map(|(ident, locs)| {
        if locs.len() <= 1 {
            return None;
        }

        let mut locations: Vec<Location> = locs
            .into_iter()
            .map(|loc| *locations.get(&loc).unwrap())
            .collect();
        locations.sort_by_key(|location| location.1);
        assert!(locations.len() > 1);
        let first_declaration = locations[0];
        let second_declaration = locations[1];

        let name: String = identifiers.get(&ident).unwrap().to_string();
        Some(CompileError::SymbolDeclaredTwice {
            name,
            first_declaration,
            second_declaration,
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
    let mut declared_symbols: BTreeMap<Ident, Vec<(SymbolKindEnum, Location)>> = BTreeMap::new();
    for (name, kind, loc) in eqlog.iter_defined_symbol() {
        let location = *locations.get(&loc).unwrap();
        declared_symbols
            .entry(name)
            .or_insert(Vec::new())
            .push((symbol_kind(kind, eqlog), location));
    }
    for decls in declared_symbols.values_mut() {
        decls.sort_by_key(|(_, location)| location.1);
    }

    eqlog
        .iter_should_be_symbol()
        .filter_map(move |(ident, kind, loc)| {
            let kind = symbol_kind(kind, eqlog);
            let name: &str = identifiers.get(&ident).unwrap().as_str();
            let location = *locations.get(&loc).unwrap();

            let decls: &[(SymbolKindEnum, Location)] = match declared_symbols.get(&ident) {
                None => {
                    return Some(CompileError::UndeclaredSymbol {
                        name: name.to_string(),
                        used_at: location,
                    });
                }
                Some(decls) => decls.as_slice(),
            };

            match decls
                .iter()
                .copied()
                .find(|(decl_kind, _)| *decl_kind == kind)
            {
                Some(_) => None,
                None => {
                    let (decl_kind, decl_location) = decls[0];
                    Some(CompileError::BadSymbolKind {
                        name: name.to_string(),
                        expected: kind,
                        found: decl_kind,
                        used_at: location,
                        declared_at: decl_location,
                    })
                }
            }
        })
}

pub fn iter_pred_arg_number_errors<'a>(
    eqlog: &'a Eqlog,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    eqlog
        .iter_pred_arg_num_should_match()
        .filter_map(|(got, expected, loc)| {
            if eqlog.are_equal_nat(got, expected) {
                return None;
            }

            let got = nat(got, eqlog);
            let expected = nat(expected, eqlog);
            let location = *locations.get(&loc).unwrap();
            Some(CompileError::PredicateArgumentNumber {
                expected,
                got,
                location,
            })
        })
}

pub fn iter_func_arg_number_errors<'a>(
    eqlog: &'a Eqlog,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    eqlog
        .iter_func_arg_num_should_match()
        .filter_map(|(got, expected, loc)| {
            if eqlog.are_equal_nat(got, expected) {
                return None;
            }

            let got = nat(got, eqlog);
            let expected = nat(expected, eqlog);
            let location = *locations.get(&loc).unwrap();
            Some(CompileError::FunctionArgumentNumber {
                expected,
                got,
                location,
            })
        })
}

pub fn iter_symbol_casing_errors<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    eqlog
        .iter_defined_symbol()
        .filter_map(|(ident, kind, loc)| {
            let name: &str = identifiers.get(&ident).unwrap().as_str();

            let location = *locations.get(&loc).unwrap();

            let symbol_kind = symbol_kind(kind, eqlog);
            match symbol_kind {
                SymbolKindEnum::Type => {
                    if name != name.to_case(Case::UpperCamel) {
                        return Some(CompileError::SymbolNotCamelCase {
                            name: name.to_string(),
                            location,
                            symbol_kind,
                        });
                    }
                }
                SymbolKindEnum::Pred | SymbolKindEnum::Func | SymbolKindEnum::Rule => {
                    if name != name.to_case(Case::Snake) {
                        return Some(CompileError::SymbolNotSnakeCase {
                            name: name.to_string(),
                            location,
                            symbol_kind,
                        });
                    }
                }
            };

            None
        })
}

pub fn check_eqlog(
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
    locations: &BTreeMap<Loc, Location>,
) -> Result<(), CompileError> {
    let first_error: Option<CompileError> = iter::empty()
        .chain(iter_symbol_declared_twice_errors(
            eqlog,
            identifiers,
            locations,
        ))
        .chain(iter_symbol_lookup_errors(eqlog, identifiers, locations))
        .chain(iter_pred_arg_number_errors(eqlog, locations))
        .chain(iter_func_arg_number_errors(eqlog, locations))
        .chain(iter_symbol_casing_errors(eqlog, identifiers, locations))
        .chain(iter_then_defined_variable_errors(eqlog, locations))
        .chain(iter_variable_introduced_in_then_errors(eqlog, locations))
        .chain(iter_wildcard_in_then_errors(eqlog, locations))
        .chain(iter_conflicting_type_errors(eqlog, locations))
        .chain(iter_undetermined_type_errors(eqlog, locations))
        .chain(iter_surjectivity_errors(eqlog, locations))
        .chain(iter_if_after_then_errors(eqlog, locations))
        .chain(iter_variable_occurs_twice(eqlog, identifiers, locations))
        .chain(iter_variable_not_snake_case_errors(
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
