mod check_epic;

use std::collections::btree_map;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::iter;

use check_epic::*;
use convert_case::Case;
use convert_case::Casing;
use itertools::Itertools;

use crate::eqlog_util::*;
use crate::error::*;
use crate::grammar_util::*;
use eqlog_eqlog::*;

fn iter_match_pattern_is_variable_errors<'a>(
    eqlog: &'a Eqlog,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    eqlog
        .iter_case_pattern_is_variable()
        .filter_map(move |loc| {
            let location = *locations.get(&loc).unwrap();
            Some(CompileError::MatchPatternIsVariable { location })
        })
}

fn iter_match_pattern_is_wildcard_errors<'a>(
    eqlog: &'a Eqlog,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    eqlog
        .iter_case_pattern_is_wildcard()
        .filter_map(move |loc| {
            let location = *locations.get(&loc).unwrap();
            Some(CompileError::MatchPatternIsWildcard { location })
        })
}

fn iter_match_pattern_ctor_arg_is_app_errors<'a>(
    eqlog: &'a Eqlog,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    eqlog.iter_pattern_ctor_arg_is_app().filter_map(move |loc| {
        let location = *locations.get(&loc).unwrap();
        Some(CompileError::MatchPatternCtorArgIsApp { location })
    })
}

fn iter_match_pattern_ctor_arg_is_not_fresh<'a>(
    eqlog: &'a Eqlog,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    eqlog
        .iter_pattern_ctor_arg_var_is_not_fresh()
        .filter_map(move |loc| {
            let location = *locations.get(&loc).unwrap();
            Some(CompileError::MatchPatternArgVarIsNotFresh { location })
        })
}

fn iter_match_conflicting_enum<'a>(
    eqlog: &'a Eqlog,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    let mut match_stmt_contains_ctor_of_enum: Vec<(StmtNode, CtorDeclNode, EnumDeclNode)> =
        eqlog.iter_match_stmt_contains_ctor_of_enum().collect();
    match_stmt_contains_ctor_of_enum.sort_by_key(|(match_stmt, _, _)| *match_stmt);

    match_stmt_contains_ctor_of_enum
        .into_iter()
        .chunk_by(|(match_stmt, _, _)| *match_stmt)
        .into_iter()
        .filter_map(move |(match_stmt, rows)| {
            let enum_ctors: BTreeMap<EnumDeclNode, CtorDeclNode> = rows
                .map(|(_, ctor_node, enum_node)| (enum_node, ctor_node))
                .collect();

            let mut enum_ctors_iter = enum_ctors.into_iter();
            let (_, first_ctor) = enum_ctors_iter.next()?;
            let (_, second_ctor) = enum_ctors_iter.next()?;

            let match_stmt_location = *locations
                .get(&eqlog.stmt_node_loc(match_stmt).unwrap())
                .unwrap();
            let first_ctor_decl_location = *locations
                .get(&eqlog.ctor_decl_node_loc(first_ctor).unwrap())
                .unwrap();
            let second_ctor_decl_location = *locations
                .get(&eqlog.ctor_decl_node_loc(second_ctor).unwrap())
                .unwrap();

            Some(CompileError::MatchConflictingEnum {
                match_stmt_location,
                first_ctor_decl_location,
                second_ctor_decl_location,
            })
        })
        // TODO: If we don't collect here we get a lifetime error. Why?
        .collect::<Vec<CompileError>>()
        .into_iter()
}

fn iter_match_stmt_contains_ctor_of_enum<'a>(
    eqlog: &'a Eqlog,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    eqlog
        .iter_match_stmt_should_contain_ctor()
        .filter_map(|(stmt, ctor)| {
            if eqlog.match_stmt_contains_ctor(stmt, ctor) {
                return None;
            }

            let match_location = *locations.get(&eqlog.stmt_node_loc(stmt).unwrap()).unwrap();
            let missing_ctor_decl_location = *locations
                .get(&eqlog.ctor_decl_node_loc(ctor).unwrap())
                .unwrap();
            Some(CompileError::MatchNotExhaustive {
                match_location,
                missing_ctor_decl_location,
            })
        })
}

pub fn iter_variable_not_snake_case_errors<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    eqlog.iter_var_term_node().filter_map(|(tm, virt_ident)| {
        let ident = eqlog.virt_real_ident(virt_ident)?;
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
    eqlog.iter_var_term_node().filter_map(|(tm, virt_ident)| {
        let scope = eqlog
            .exit_scope(eqlog.rule_descendant_term(tm).unwrap())
            .unwrap();
        let el_name = eqlog.semantic_name(virt_ident, scope).unwrap();

        let has_second_occurrence = eqlog
            .iter_var_term_node()
            .find(|(tm0, virt_ident0)| {
                if eqlog.are_equal_term_node(tm, *tm0) {
                    return false;
                }

                let scope0 = eqlog
                    .exit_scope(eqlog.rule_descendant_term(*tm0).unwrap())
                    .unwrap();
                let el_name0 = eqlog.semantic_name(*virt_ident0, scope0).unwrap();
                eqlog.are_equal_el_name(el_name, el_name0)
            })
            .is_some();

        if has_second_occurrence {
            return None;
        }

        let ident = eqlog.virt_real_ident(virt_ident)?;
        // TODO: This doesn't actually hold; we're ignoring occurs-only-once errors at the
        // moment if they arise from purely virtual identifiers. But why does it not hold?
        //.expect("Desugaring should never result in compilation errors");

        let name: &str = identifiers.get(&ident).unwrap().as_str();

        let loc = eqlog.term_node_loc(tm).unwrap();
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
    let mut el_type: BTreeMap<El, ElementType> = BTreeMap::new();
    eqlog
        .iter_el_type()
        .filter_map(move |(el, ty)| match el_type.entry(el) {
            btree_map::Entry::Vacant(vacant) => {
                vacant.insert(ty);
                None
            }
            btree_map::Entry::Occupied(occupied) => {
                if eqlog.are_equal_element_type(*occupied.get(), ty) {
                    None
                } else {
                    Some(el)
                }
            }
        })
        .flat_map(move |el| {
            eqlog.iter_semantic_el().filter_map(move |(tm, _, e)| {
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

pub fn iter_symbol_declared_twice_errors<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    let mut symbols: BTreeMap<(SymbolScope, Ident), Vec<Loc>> = BTreeMap::new();
    for (scope, name, _, loc) in eqlog.iter_accessible_symbol() {
        symbols.entry((scope, name)).or_insert(Vec::new()).push(loc);
    }

    symbols.into_iter().filter_map(|((_, ident), locs)| {
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
        .iter_accessible_symbol()
        .filter_map(|(_scope, ident, kind, loc)| {
            let name: &str = identifiers.get(&ident).unwrap().as_str();

            let location = *locations.get(&loc).unwrap();

            let symbol_kind = eqlog.symbol_kind_case(kind);
            match symbol_kind {
                SymbolKindCase::ModelSymbol()
                | SymbolKindCase::TypeSymbol()
                | SymbolKindCase::EnumSymbol()
                | SymbolKindCase::CtorSymbol() => {
                    if name != name.to_case(Case::UpperCamel) {
                        return Some(CompileError::SymbolNotCamelCase {
                            name: name.to_string(),
                            location,
                            symbol_kind,
                        });
                    }
                }
                SymbolKindCase::PredSymbol()
                | SymbolKindCase::FuncSymbol()
                | SymbolKindCase::RuleSymbol() => {
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

pub fn iter_illegal_rel_arg_errors<'a>(
    eqlog: &'a Eqlog,
    _identifiers: &'a BTreeMap<Ident, String>,
    locations: &'a BTreeMap<Loc, Location>,
) -> impl 'a + Iterator<Item = CompileError> {
    eqlog
        .iter_illegal_member_type_expr_in_signature()
        .filter_map(move |type_expr_node| {
            let loc = eqlog.type_expr_node_loc(type_expr_node)?;
            let location = *locations.get(&loc).unwrap();
            Some(CompileError::IllegalMemberTypeExprInArgDecl { location })
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
        .chain(iter_match_pattern_is_variable_errors(eqlog, locations))
        .chain(iter_match_pattern_is_wildcard_errors(eqlog, locations))
        .chain(iter_match_pattern_ctor_arg_is_app_errors(eqlog, locations))
        .chain(iter_match_pattern_ctor_arg_is_not_fresh(eqlog, locations))
        .chain(iter_match_conflicting_enum(eqlog, locations))
        .chain(iter_match_stmt_contains_ctor_of_enum(eqlog, locations))
        .chain(iter_undetermined_type_errors(eqlog, locations))
        .chain(iter_surjectivity_errors(eqlog, locations))
        .chain(iter_variable_occurs_twice(eqlog, identifiers, locations))
        .chain(iter_variable_not_snake_case_errors(
            eqlog,
            identifiers,
            locations,
        ))
        .chain(iter_enum_ctors_not_surjective_errors(
            eqlog,
            identifiers,
            locations,
        ))
        .chain(iter_illegal_rel_arg_errors(eqlog, identifiers, locations))
        .min();

    if let Some(err) = first_error {
        Err(err)
    } else {
        Ok(())
    }
}
