use crate::eqlog_util::*;
use crate::flat_eqlog::*;
use crate::fmt_util::*;
use crate::rust_gen::{IndexName, OrderName};
use convert_case::{Case, Casing};
use eqlog_eqlog::*;
use indoc::writedoc;
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Display, Formatter};

use Case::{ScreamingSnake, Snake, UpperCamel};

fn display_rel_row_type<'a>(rel: Rel, eqlog: &'a Eqlog) -> impl 'a + Display {
    FmtFn(move |f| {
        let arity_len = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog).len();
        write!(f, "[u32; {arity_len}]")
    })
}

fn display_table_struct<'a>(
    rel: Rel,
    indices: &'a BTreeSet<&'a IndexSpec>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        let rel_camel = rel_snake.to_case(UpperCamel);

        let arity = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);

        let row_type = display_rel_row_type(rel, eqlog).to_string();
        let row_type = row_type.as_str();

        let index_fields = indices
            .iter()
            .map(|index| {
                FmtFn(move |f| {
                    let index_name = IndexName(index);
                    write!(f, "index_{index_name}: BTreeSet<{row_type}>,")
                })
            })
            .format("\n");

        let types: BTreeSet<Type> = arity.iter().copied().collect();
        let element_index_fields = types
            .iter()
            .copied()
            .map(|typ| {
                FmtFn(move |f| {
                    let type_snake = display_type(typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    write!(
                        f,
                        "element_index_{type_snake}: BTreeMap<u32, Vec<{row_type}>>,"
                    )
                })
            })
            .format("\n");

        writedoc! {f, "
            #[derive(Clone, Hash, Debug)]
            pub struct {rel_camel}Table {{
            {index_fields}

            {element_index_fields}
            }}
        "}
    })
}

fn display_table_new_fn_signature<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        let rel_camel = rel_snake.to_case(UpperCamel);
        write!(
            f,
            "fn {symbol_prefix}_new_{rel_snake}_table() -> &'static mut {rel_camel}Table"
        )
    })
}

fn display_table_new_fn<'a>(
    rel: Rel,
    indices: &'a BTreeSet<&'a IndexSpec>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let signature = display_table_new_fn_signature(rel, eqlog, identifiers, symbol_prefix);
        let rel_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        let rel_camel = rel_snake.to_case(UpperCamel);
        let index_fields = indices
            .iter()
            .map(|index| {
                FmtFn(move |f| {
                    let index_name = IndexName(index);
                    write!(f, "index_{index_name}: BTreeSet::new(),")
                })
            })
            .format("\n");
        let arity = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
        let types: BTreeSet<Type> = arity.iter().copied().collect();
        let element_index_fields = types
            .iter()
            .copied()
            .map(|typ| {
                FmtFn(move |f| {
                    let type_snake = display_type(typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    write!(f, "element_index_{type_snake}: BTreeMap::new(),")
                })
            })
            .format("\n");

        writedoc! {f, r#"
            #[unsafe(no_mangle)]
            pub extern "Rust" {signature} {{
            let table = Box::new({rel_camel}Table {{
            {index_fields}

            {element_index_fields}
            }});

            Box::leak(table)
            }}
        "#}
    })
}

pub fn display_table_new_fn_decl<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let signature = display_table_new_fn_signature(rel, eqlog, identifiers, symbol_prefix);
        writedoc! {f, "
            safe {signature};
        "}
    })
}

pub fn display_table_drop_fn_decl<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let signature = display_table_drop_fn_signature(rel, eqlog, identifiers, symbol_prefix);
        writedoc! {f, "
            safe {signature};
        "}
    })
}

pub fn display_contains_fn_decl<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let signature = display_contains_fn_signature(rel, eqlog, identifiers, symbol_prefix);
        writedoc! {f, "
            safe {signature};
        "}
    })
}

pub fn display_insert_fn_decl<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let signature = display_insert_fn_signature(rel, eqlog, identifiers, symbol_prefix);
        writedoc! {f, "
            safe {signature};
        "}
    })
}

pub fn display_drain_with_element_fn_decl<'a>(
    rel: Rel,
    typ: Type,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let signature =
            display_drain_with_element_fn_signature(rel, typ, eqlog, identifiers, symbol_prefix);
        writedoc! {f, "
            safe {signature};
        "}
    })
}

pub fn display_move_new_to_old_fn_decl<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let signature =
            display_move_new_to_old_fn_signature(rel, eqlog, identifiers, symbol_prefix);
        writedoc! {f, "
            safe {signature};
        "}
    })
}

pub fn display_has_new_data_fn_decl<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let signature = display_has_new_data_fn_signature(rel, eqlog, identifiers, symbol_prefix);
        writedoc! {f, "
            safe {signature};
        "}
    })
}

pub fn display_iter_fn_decl<'a>(
    query_spec: &'a QuerySpec,
    indices: &'a Vec<IndexSpec>,
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let fn_name = display_iter_fn_name(rel, query_spec, eqlog, identifiers, symbol_prefix);
        let rel_camel = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        let index_num = indices.len();
        let fn_args = query_spec
            .projections
            .iter()
            .copied()
            .map(|p| FmtFn(move |f| write!(f, "arg{p}: u32")))
            .format(", ");

        writedoc! {f, "
            safe fn {fn_name}(table: &{rel_camel}Table, {fn_args}) -> {rel_camel}RangeIter{index_num};
        "}
    })
}

pub fn display_iter_next_fn_decl<'a>(
    query_spec: &'a QuerySpec,
    indices: &'a Vec<IndexSpec>,
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let signature = display_iter_next_fn_signature(
            query_spec,
            indices,
            rel,
            eqlog,
            identifiers,
            symbol_prefix,
        );
        writedoc! {f, "
            safe {signature};
        "}
    })
}

pub fn display_weight_static_decl<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let signature = display_weight_static_signature(rel, eqlog, identifiers, symbol_prefix);
        writedoc! {f, "
            safe {signature};
        "}
    })
}

fn display_table_drop_fn_signature<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        let rel_camel = rel_snake.to_case(UpperCamel);
        write!(
            f,
            "fn {symbol_prefix}_drop_{rel_snake}_table(ptr: NonNull<*mut {rel_camel}Table>)"
        )
    })
}

fn display_table_drop_fn<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let signature = display_table_drop_fn_signature(rel, eqlog, identifiers, symbol_prefix);
        writedoc! {f, r#"
            #[unsafe(no_mangle)]
            pub unsafe {signature} {{
            drop(Box::from_raw(ptr.as_ptr()));
            }}
        "#}
    })
}

fn display_permute_fn<'a>(order: &'a [usize], rel: Rel, eqlog: &'a Eqlog) -> impl 'a + Display {
    FmtFn(move |f| {
        let order_name = OrderName(order);
        let row_type = display_rel_row_type(rel, eqlog).to_string();
        let arity_len = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog).len();
        let permuted_row_args = (0..arity_len)
            .map(|i| {
                FmtFn(move |f| {
                    let j = order[i];
                    write!(f, "row[{j}]")
                })
            })
            .format(", ");

        writedoc! {f, "
            #[allow(unused)]
            fn permute{order_name}(row: {row_type}) -> {row_type} {{
            [{permuted_row_args}]
            }}
        "}
    })
}

fn display_permute_inverse_fn<'a>(
    order: &'a [usize],
    rel: Rel,
    eqlog: &'a Eqlog,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let order_name = OrderName(order);
        let row_type = display_rel_row_type(rel, eqlog).to_string();
        let arity_len = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog).len();
        let row_args = (0..arity_len)
            .map(|i| {
                FmtFn(move |f| {
                    let j = order.iter().copied().position(|j| j == i).unwrap();
                    write!(f, "permuted_row[{j}]")
                })
            })
            .format(", ");

        writedoc! {f, "
            #[allow(unused)]
            fn permute_inverse{order_name}(permuted_row: {row_type}) -> {row_type} {{
            [{row_args}]
            }}
        "}
    })
}

fn display_contains_fn_signature<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_camel = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        let rel_snake = rel_camel.to_case(Snake);
        let row_type = display_rel_row_type(rel, eqlog).to_string();
        write!(
            f,
            "fn {symbol_prefix}_{rel_snake}_contains(table: &{rel_camel}Table, row: {row_type}) -> bool"
        )
    })
}

fn display_contains_fn<'a>(
    rel: Rel,
    index_selection: &'a BTreeMap<QuerySpec, Vec<IndexSpec>>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let signature = display_contains_fn_signature(rel, eqlog, identifiers, symbol_prefix);
        let indices = index_selection.get(&QuerySpec::all()).unwrap();

        let checks = indices
            .iter()
            .map(|index| {
                FmtFn(|f| {
                    let index_name = IndexName(index);
                    let order_name = OrderName(&index.order);
                    write!(
                        f,
                        "table.index_{index_name}.contains(&permute{order_name}(row))"
                    )
                })
            })
            .format(" || ");

        writedoc! {f, r#"
            #[allow(unused)]
            pub extern "Rust" {signature} {{
            {checks}
            }}
        "#}
    })
}

pub struct DiagonalCheck<'a>(pub &'a BTreeSet<BTreeSet<usize>>);
impl<'a> Display for DiagonalCheck<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let diags = &self.0;
        let all_clauses = diags.iter().format_with(" && ", |diag, f| {
            let diag_clauses = diag
                .iter()
                .zip(diag.iter().skip(1))
                .format_with(" && ", |(prev, next), f| {
                    f(&format_args!("row[{prev}] == row[{next}]"))
                });
            f(&format_args!("{diag_clauses}"))
        });
        write!(f, "{all_clauses}")
    }
}

fn display_insert_fn_signature<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_camel = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        let rel_snake = rel_camel.to_case(Snake);
        let row_type = display_rel_row_type(rel, eqlog).to_string();
        write!(
            f,
            "fn {symbol_prefix}_{rel_snake}_insert(table: &mut {rel_camel}Table, row: {row_type}) -> bool"
        )
    })
}

fn display_insert_fn<'a>(
    rel: Rel,
    indices: &'a BTreeSet<&'a IndexSpec>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let signature = display_insert_fn_signature(rel, eqlog, identifiers, symbol_prefix);

        let primary_new = indices
            .iter()
            .copied()
            .find(
                |IndexSpec {
                     order: _,
                     diagonals,
                     age,
                 }| { diagonals.is_empty() && *age == IndexAge::New },
            )
            .expect("Every relation should have a primary new index");
        let primary_old = indices
            .iter()
            .find(
                |IndexSpec {
                     order: _,
                     diagonals,
                     age,
                 }| { diagonals.is_empty() && *age == IndexAge::Old },
            )
            .expect("Every relation should have a primary old index");

        let primary_new_order = OrderName(&primary_new.order);
        let primary_old_order = OrderName(&primary_old.order);

        let other_new_inserts = indices
            .into_iter()
            .copied()
            .filter(|index| index.age == IndexAge::New && *index != primary_new)
            .map(|index| {
                FmtFn(move |f| {
                    let index_name = IndexName(index);
                    let order = OrderName(&index.order);
                    if index.diagonals.is_empty() {
                        writedoc! {f, "
                            table.index_{index_name}.insert(permute{order}(row));"
                        }
                    } else {
                        let check = DiagonalCheck(&index.diagonals);
                        writedoc! {f, "
                            let check = {check};
                            if check {{
                                table.index_{index_name}.insert(permute{order}(row));
                            }}
                        "}
                    }
                })
            })
            .format("\n");

        let arity = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
        let element_inserts = arity
            .iter()
            .copied()
            .enumerate()
            .map(|(i, typ)| {
                FmtFn(move |f| {
                    let type_snake = display_type(typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    writedoc! {f, "
                    match table.element_index_{type_snake}.entry(row[{i}]) {{
                    btree_map::Entry::Occupied(mut entry) => {{
                    entry.get_mut().push(row);
                    }}
                    btree_map::Entry::Vacant(entry) => {{
                    entry.insert(vec![row]);
                    }}
                    }}
                "}
                })
            })
            .format("\n");

        let primary_old = IndexName(primary_old);
        let primary_new = IndexName(primary_new);

        writedoc! {f, r#"
            #[allow(unused)]
            pub extern "Rust" {signature} {{
            if table.index_{primary_old}.contains(&permute{primary_old_order}(row)) {{
            return false;
            }}
            if !table.index_{primary_new}.insert(permute{primary_new_order}(row)) {{
            return false;
            }}

            {other_new_inserts}

            {element_inserts}

            true
            }}
        "#}
    })
}

fn display_remove_from_row_indices_fn<'a>(
    rel: Rel,
    indices: &'a BTreeSet<&'a IndexSpec>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let row_type = display_rel_row_type(rel, eqlog).to_string();
        let rel_camel = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);

        let primary_new = indices
            .iter()
            .copied()
            .find(
                |IndexSpec {
                     order: _,
                     diagonals,
                     age,
                 }| { diagonals.is_empty() && *age == IndexAge::New },
            )
            .expect("Every relation should have a primary new index");
        let primary_old = indices
            .iter()
            .copied()
            .find(
                |IndexSpec {
                     order: _,
                     diagonals,
                     age,
                 }| { diagonals.is_empty() && *age == IndexAge::Old },
            )
            .expect("Every relation should have a primary old index");

        let primary_new_order = OrderName(&primary_new.order);
        let primary_old_order = OrderName(&primary_old.order);

        let other_new_removes = indices
            .into_iter()
            .copied()
            .filter(|index| index.age == IndexAge::New && *index != primary_new)
            .map(|index| {
                FmtFn(move |f| {
                    let index_name = IndexName(index);
                    let order = OrderName(&index.order);
                    if index.diagonals.is_empty() {
                        writedoc! {f, "
                            table.index_{index_name}.remove(&permute{order}(row));"
                        }
                    } else {
                        let check = DiagonalCheck(&index.diagonals);
                        writedoc! {f, "
                        let check = {check};
                        if check {{
                            table.index_{index_name}.remove(&permute{order}(row));
                        }}
                    "}
                    }
                })
            })
            .format("\n");

        let other_old_removes = indices
            .into_iter()
            .copied()
            .filter(|index| index.age == IndexAge::Old && *index != primary_old)
            .map(|index| {
                FmtFn(move |f| {
                    let index_name = IndexName(index);
                    let order = OrderName(&index.order);
                    if index.diagonals.is_empty() {
                        writedoc! {f, "
                            table.index_{index_name}.remove(&permute{order}(row));"
                        }
                    } else {
                        let check = DiagonalCheck(&index.diagonals);
                        writedoc! {f, "
                        let check = {check};
                        if check {{
                            table.index_{index_name}.remove(&permute{order}(row));
                        }}
                    "}
                    }
                })
            })
            .format("\n");

        let primary_new = IndexName(primary_new);
        let primary_old = IndexName(primary_old);

        writedoc! {f, "
            fn remove_from_row_indices(table: &mut {rel_camel}Table, row: {row_type}) -> bool {{
                if table.index_{primary_new}.remove(&permute{primary_new_order}(row)) {{
                    {other_new_removes}
                    true
                }} else if table.index_{primary_old}.remove(&permute{primary_old_order}(row)) {{
                    {other_old_removes}
                    true
                }} else {{
                    false
                }}
            }}
        "}
    })
}

fn display_drain_with_element_fn_signature<'a>(
    rel: Rel,
    typ: Type,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_camel = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        let rel_snake = rel_camel.to_case(Snake);
        let row_type = display_rel_row_type(rel, eqlog).to_string();
        let type_snake = display_type(typ, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        write!(
            f,
            "fn {symbol_prefix}_{rel_snake}_drain_with_element_{type_snake}(table: &mut {rel_camel}Table, el: u32) -> Vec<{row_type}>"
        )
    })
}

fn display_drain_with_element_fns<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    let types: BTreeSet<Type> = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog)
        .into_iter()
        .collect();
    types
        .into_iter()
        .map(move |typ| {
            FmtFn(move |f| {
                let signature = display_drain_with_element_fn_signature(
                    rel,
                    typ,
                    eqlog,
                    identifiers,
                    symbol_prefix,
                );
                let type_snake = display_type(typ, eqlog, identifiers)
                    .to_string()
                    .to_case(Snake);

                writedoc! {f, r#"
            #[unsafe(no_mangle)]
            pub extern "Rust" {signature} {{
                let mut rows = table.element_index_{type_snake}.remove(&el).unwrap_or_default();

                let mut i = 0;
                while i < rows.len() {{
                    let row = rows[i];
                    if remove_from_row_indices(table, row) {{
                        rows.swap_remove(i);
                    }} else {{
                        i += 1;
                    }}
                }}

                rows
            }}
        "#}
            })
        })
        .format("\n")
}

fn display_move_new_to_old_fn_signature<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        let rel_camel = rel_snake.to_case(UpperCamel);
        write!(
            f,
            "fn {symbol_prefix}_{rel_snake}_move_new_to_old(table: &mut {rel_camel}Table)"
        )
    })
}

fn display_move_new_to_old_fn<'a>(
    rel: Rel,
    indices: &'a BTreeSet<&IndexSpec>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let signature =
            display_move_new_to_old_fn_signature(rel, eqlog, identifiers, symbol_prefix);
        let primary_new = indices
            .iter()
            .copied()
            .find(
                |IndexSpec {
                     order: _,
                     diagonals,
                     age,
                 }| { diagonals.is_empty() && *age == IndexAge::New },
            )
            .expect("Every relation should have a primary new index");
        let primary_new_order = OrderName(&primary_new.order);
        let primary_new = IndexName(primary_new);

        let old_inserts = indices
            .iter()
            .copied()
            .filter(|index| index.age == IndexAge::Old)
            .map(|index| {
                FmtFn(|f| {
                    let index_order = OrderName(&index.order);
                    let diagonals = &index.diagonals;
                    let index = IndexName(index);
                    if diagonals.is_empty() {
                        writedoc! {f, "
                            table.index_{index}.insert(permute{index_order}(row));
                        "}
                    } else {
                        let check = DiagonalCheck(&diagonals);
                        writedoc! {f, "
                            if {check} {{
                            table.index_{index}.insert(permute{index_order}(row));
                            }}
                        "}
                    }
                })
            })
            .format("\n");

        let clear_new_indices = indices
            .iter()
            .copied()
            .filter(|index| index.age == IndexAge::New)
            .map(|index| {
                FmtFn(move |f| {
                    let index_name = IndexName(index);
                    writedoc! {f, "
                        table.index_{index_name}.clear();
                    "}
                })
            })
            .format("\n");

        writedoc! {f, r#"
            #[unsafe(no_mangle)]
            pub extern "Rust" {signature} {{
            for row in table.index_{primary_new}.iter().copied() {{
            let row = permute_inverse{primary_new_order}(row);
            {old_inserts}
            }}

            {clear_new_indices}
            }}
        "#}
    })
}

fn display_has_new_data_fn_signature<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        let rel_camel = rel_snake.to_case(UpperCamel);
        write!(
            f,
            "fn {symbol_prefix}_{rel_snake}_has_new_data(table: &{rel_camel}Table) -> bool"
        )
    })
}

fn display_has_new_data_fn<'a>(
    rel: Rel,
    indices: &'a BTreeSet<&IndexSpec>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let signature = display_has_new_data_fn_signature(rel, eqlog, identifiers, symbol_prefix);
        let primary_new = indices
            .iter()
            .copied()
            .find(
                |IndexSpec {
                     order: _,
                     diagonals,
                     age,
                 }| { diagonals.is_empty() && *age == IndexAge::New },
            )
            .expect("Every relation should have a primary new index");
        let primary_new = IndexName(primary_new);

        writedoc! {f, r#"
            #[unsafe(no_mangle)]
            pub extern "Rust" {signature} {{
            !table.index_{primary_new}.is_empty()
            }}
        "#}
    })
}

fn display_iter_ty<'a>(
    index_num: usize,
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_camel = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);

        let row_type = display_rel_row_type(rel, eqlog).to_string();
        let row_type = row_type.as_str();
        let fields = (0..index_num)
            .map(|_| FmtFn(move |f| write!(f, "btree_set::Range<'a, {row_type}>, ")))
            .format("");

        write!(
            f,
            "pub type {rel_camel}RangeIter{index_num}<'a> = ({fields});"
        )
    })
}

pub fn display_iter_ty_structs<'a>(
    rel: Rel,
    index_selection: &'a BTreeMap<QuerySpec, Vec<IndexSpec>>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    let query_indices_lens: BTreeSet<usize> = index_selection
        .values()
        .map(|indices| indices.len())
        .collect();
    query_indices_lens
        .into_iter()
        .map(move |i| display_iter_ty(i, rel, eqlog, identifiers))
        .format("\n")
}

fn display_iter_fn_name<'a>(
    rel: Rel,
    query_spec: &'a QuerySpec,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        let age_str = match query_spec.age {
            QueryAge::New => "new",
            QueryAge::Old => "old",
            QueryAge::All => "all",
        };
        let projections = query_spec
            .projections
            .iter()
            .map(|proj| FmtFn(move |f| write!(f, "_{proj}")))
            .format("");

        let diagonals = query_spec
            .diagonals
            .iter()
            .map(|diag| {
                FmtFn(move |f| {
                    let diag = diag
                        .iter()
                        .map(|d| FmtFn(move |f| write!(f, "_{d}")))
                        .format("");
                    write!(f, "_diagonal{diag}")
                })
            })
            .format("");

        write!(
            f,
            "{symbol_prefix}_iter_{rel_snake}_{age_str}{projections}{diagonals}"
        )
    })
}

fn display_iter_fn<'a>(
    query_spec: &'a QuerySpec,
    indices: &'a Vec<IndexSpec>,
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let fn_name = display_iter_fn_name(rel, query_spec, eqlog, identifiers, symbol_prefix);
        let rel_camel = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);

        let row_type = display_rel_row_type(rel, eqlog).to_string();
        let row_type = row_type.as_str();

        let fn_args = query_spec
            .projections
            .iter()
            .copied()
            .map(|p| FmtFn(move |f| write!(f, "arg{p}: u32")))
            .format(", ");
        let index_num = indices.len();

        let arity_len = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog).len();
        let fixed_arg_len = query_spec.projections.len();
        let open_arg_len = arity_len - fixed_arg_len;

        let range_defs = indices
            .iter()
            .enumerate()
            .map(|(i, index)| {
                let index_name = IndexName(index);

                let fixed_args = index.order[..fixed_arg_len]
                    .iter()
                    .map(|i| FmtFn(move |f| write!(f, "arg{i}, ")))
                    .format("")
                    .to_string();

                let open_args_min = (0..open_arg_len).map(|_| "u32::MIN, ").format("");
                let open_args_max = (0..open_arg_len).map(|_| "u32::MAX, ").format("");

                FmtFn(move |f| {
                    writedoc! {f, "
                        let lower: {row_type} = [{fixed_args}{open_args_min}];
                        let upper: {row_type} = [{fixed_args}{open_args_max}];
                        let range{i} = table.index_{index_name}.range(lower..=upper);
                    "}
                })
            })
            .format("\n");

        let range_args = (0..indices.len())
            .map(|i| FmtFn(move |f| write!(f, "range{i}, ")))
            .format("");

        writedoc! {f, r#"
            #[unsafe(no_mangle)]
            pub extern "Rust" fn {fn_name}(table: &{rel_camel}Table, {fn_args}) -> {rel_camel}RangeIter{index_num} {{
            {range_defs}
            ({range_args})
            }}
        "#}
    })
}

fn display_iter_next_fn_signature<'a>(
    query_spec: &'a QuerySpec,
    indices: &'a Vec<IndexSpec>,
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_camel = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        let iter_fn = display_iter_fn_name(rel, query_spec, eqlog, identifiers, symbol_prefix);
        let index_num = indices.len();
        let row_type = display_rel_row_type(rel, eqlog);
        write!(
            f,
            "fn {iter_fn}_next(it: &mut {rel_camel}RangeIter{index_num}) -> Option<{row_type}>"
        )
    })
}

fn display_iter_next_fn<'a>(
    query_spec: &'a QuerySpec,
    indices: &'a Vec<IndexSpec>,
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let signature = display_iter_next_fn_signature(
            query_spec,
            indices,
            rel,
            eqlog,
            identifiers,
            symbol_prefix,
        );

        let blocks = indices
            .iter()
            .enumerate()
            .map(|(i, index)| {
                FmtFn(move |f| {
                    let order_name = OrderName(index.order.as_slice());
                    writedoc! {f, "
                        if let Some(permuted_row) = it.{i}.next() {{
                            return Some(permute_inverse{order_name}(*permuted_row));
                        }}
                    "}
                })
            })
            .format("\n");

        writedoc! {f, r#"
            #[unsafe(no_mangle)]
            pub extern "Rust" {signature} {{
            {blocks}
            None
            }}
        "#}
    })
}

fn display_weight_static_signature<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_screaming_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(ScreamingSnake);
        write!(
            f,
            "static {symbol_prefix}_{rel_screaming_snake}_WEIGHT: u32"
        )
    })
}

fn display_weight_static<'a>(
    rel: Rel,
    indices: &'a BTreeSet<&IndexSpec>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let signature = display_weight_static_signature(rel, eqlog, identifiers, symbol_prefix);
        let arity = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
        let tuple_weight = arity.len();
        let el_lookup_weight = tuple_weight;
        let indices_weight = indices.len() * tuple_weight;
        let weight = el_lookup_weight + indices_weight;
        writedoc! {f, r#"
            #[unsafe(no_mangle)]
            pub {signature} = {weight};
        "#}
    })
}

pub fn display_table_lib<'a>(
    rel: Rel,
    index_selection: &'a BTreeMap<QuerySpec, Vec<IndexSpec>>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let indices: BTreeSet<&IndexSpec> = index_selection
            .iter()
            .flat_map(|(_, indices)| indices)
            .collect();

        let index_orders: BTreeSet<&[usize]> =
            indices.iter().map(|index| &index.order[..]).collect();
        let strct = display_table_struct(rel, &indices, eqlog, identifiers);
        let new_fn = display_table_new_fn(rel, &indices, eqlog, identifiers, symbol_prefix);
        let drop_fn = display_table_drop_fn(rel, eqlog, identifiers, symbol_prefix);
        let permutation_fns = index_orders
            .iter()
            .copied()
            .map(|order| {
                FmtFn(move |f| {
                    let permute = display_permute_fn(order, rel, eqlog);
                    let permute_inverse = display_permute_inverse_fn(order, rel, eqlog);
                    writedoc! {f, "
                        {permute}
                        {permute_inverse}
                    "}
                })
            })
            .format("");

        let contains_fn =
            display_contains_fn(rel, &index_selection, eqlog, identifiers, symbol_prefix);
        let insert_fn = display_insert_fn(rel, &indices, eqlog, identifiers, symbol_prefix);

        let remove_from_row_indices_fn =
            display_remove_from_row_indices_fn(rel, &indices, eqlog, identifiers);
        let drain_with_element_fns =
            display_drain_with_element_fns(rel, eqlog, identifiers, symbol_prefix);

        let move_new_to_old_fn =
            display_move_new_to_old_fn(rel, &indices, eqlog, identifiers, symbol_prefix);
        let has_new_data_fn =
            display_has_new_data_fn(rel, &indices, eqlog, identifiers, symbol_prefix);

        let iter_ty_structs = display_iter_ty_structs(rel, index_selection, eqlog, identifiers);
        let iter_fns = index_selection
            .iter()
            .map(|(query_spec, indices)| {
                display_iter_fn(query_spec, indices, rel, eqlog, identifiers, symbol_prefix)
            })
            .format("\n");

        let iter_next_fns = index_selection
            .iter()
            .map(|(query_spec, indices)| {
                display_iter_next_fn(query_spec, indices, rel, eqlog, identifiers, symbol_prefix)
            })
            .format("\n");

        let weight_static = display_weight_static(rel, &indices, eqlog, identifiers, symbol_prefix);

        writedoc! {f, "
            use std::collections::{{BTreeSet, BTreeMap}};
            use std::collections::btree_set;
            use std::collections::btree_map;
            use std::ptr::NonNull;

            {strct}
            {new_fn}
            {drop_fn}

            {permutation_fns}

            {contains_fn}
            {insert_fn}

            {remove_from_row_indices_fn}
            {drain_with_element_fns}

            {move_new_to_old_fn}
            {has_new_data_fn}

            {iter_ty_structs}

            {iter_fns}
            {iter_next_fns}

            {weight_static}
        "}
    })
}
