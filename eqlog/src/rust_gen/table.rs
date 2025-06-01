use crate::eqlog_util::*;
use crate::flat_eqlog::*;
use crate::fmt_util::*;
use convert_case::{Case, Casing};
use eqlog_eqlog::*;
use indoc::writedoc;
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Display, Formatter};

use Case::{Snake, UpperCamel, UpperSnake};

pub fn display_rel_row_type<'a>(rel: Rel, eqlog: &'a Eqlog) -> impl 'a + Display {
    FmtFn(move |f| {
        let arity_len = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog).len();
        write!(f, "[u32; {arity_len}]")
    })
}

/// Displays the tuple type of the arguments of a function.
pub fn display_func_args_type<'a>(func: Func, eqlog: &'a Eqlog) -> impl 'a + Display {
    FmtFn(move |f| {
        let dom_list = eqlog.flat_domain(func).unwrap();
        let arity_len = type_list_vec(dom_list, eqlog).len();
        write!(f, "[u32; {arity_len}]")
    })
}

#[derive(Copy, Clone)]
struct OrderName<'a>(&'a [usize]);
impl<'a> Display for OrderName<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            self.0
                .iter()
                .format_with("", |i, f| f(&format_args!("_{i}")))
        )
    }
}

#[derive(Copy, Clone)]
struct IndexName<'a>(&'a IndexSpec);

impl<'a> Display for IndexName<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let index = self.0;
        let age_str = match index.age {
            IndexAge::New => "new",
            IndexAge::Old => "old",
        };
        write!(f, "{age_str}")?;
        for i in index.order.iter() {
            write!(f, "_{i}")?;
        }
        for diag in index.diagonals.iter() {
            write!(f, "_diagonal")?;
            for d in diag.iter() {
                write!(f, "_{d}")?;
            }
        }
        Ok(())
    }
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
        let arity_len = arity.len();

        let row_type = display_rel_row_type(rel, eqlog).to_string();
        let row_type = row_type.as_str();

        let index_fields = indices
            .iter()
            .map(|index| {
                FmtFn(move |f| {
                    let index_name = IndexName(index);
                    write!(f, "index_{index_name}: btree_set::BTreeSet{arity_len},")
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
            pub struct {rel_camel}Table {{
            {index_fields}

            {element_index_fields}
            }}
        "}
    })
}

pub fn display_table_struct_decl<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| {
        let rel_camel = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        writedoc! {f, "
            #[allow(unused)]
            pub struct {rel_camel}Table {{
                _data: (),
                _marker: core::marker::PhantomData<(*mut u8, core::marker::PhantomPinned)>,
            }}
        "}
    })
}

pub fn display_table_new_fn_name<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        write!(f, "new_{rel_snake}_table")
    })
}

fn display_table_new_fn_signature<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let fn_name = display_table_new_fn_name(rel, eqlog, identifiers);
        let rel_camel = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        write!(f, "fn {fn_name}() -> &'static mut {rel_camel}Table")
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
        let fn_name = display_table_new_fn_name(rel, eqlog, identifiers);
        let signature = display_table_new_fn_signature(rel, eqlog, identifiers);
        let rel_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        let rel_camel = rel_snake.to_case(UpperCamel);
        let arity = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
        let arity_len = arity.len();
        let index_fields = indices
            .iter()
            .map(|index| {
                FmtFn(move |f| {
                    let index_name = IndexName(index);
                    write!(f, "index_{index_name}: btree_set::new{arity_len}(),")
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
                    write!(f, "element_index_{type_snake}: BTreeMap::new(),")
                })
            })
            .format("\n");

        writedoc! {f, r#"
            #[unsafe(export_name = "{symbol_prefix}_{fn_name}")]
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
        let fn_name = display_table_new_fn_name(rel, eqlog, identifiers);
        let signature = display_table_new_fn_signature(rel, eqlog, identifiers);
        writedoc! {f, "
            #[link_name = \"{symbol_prefix}_{fn_name}\"]
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
        let fn_name = display_table_drop_fn_name(rel, eqlog, identifiers);
        let signature = display_table_drop_fn_signature(rel, eqlog, identifiers);
        writedoc! {f, "
            #[link_name = \"{symbol_prefix}_{fn_name}\"]
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
        let fn_name = display_contains_fn_name(rel, eqlog, identifiers);
        let signature = display_contains_fn_signature(rel, eqlog, identifiers);
        writedoc! {f, "
            #[link_name = \"{symbol_prefix}_{fn_name}\"]
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
        let fn_name = display_insert_fn_name(rel, eqlog, identifiers);
        let signature = display_insert_fn_signature(rel, eqlog, identifiers);
        writedoc! {f, "
            #[link_name = \"{symbol_prefix}_{fn_name}\"]
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
        let fn_name = display_drain_with_element_fn_name(rel, typ, eqlog, identifiers);
        let signature = display_drain_with_element_fn_signature(rel, typ, eqlog, identifiers);
        writedoc! {f, "
            #[link_name = \"{symbol_prefix}_{fn_name}\"]
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
        let fn_name = display_move_new_to_old_fn_name(rel, eqlog, identifiers);
        let signature = display_move_new_to_old_fn_signature(rel, eqlog, identifiers);
        writedoc! {f, "
            #[link_name = \"{symbol_prefix}_{fn_name}\"]
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
        let fn_name = display_has_new_data_fn_name(rel, eqlog, identifiers);
        let signature = display_has_new_data_fn_signature(rel, eqlog, identifiers);
        writedoc! {f, "
            #[link_name = \"{symbol_prefix}_{fn_name}\"]
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
        let fn_name = display_iter_fn_name(rel, query_spec, eqlog, identifiers);
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
            #[link_name = \"{symbol_prefix}_{fn_name}\"]
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
        let fn_name = display_iter_next_fn_name(query_spec, rel, eqlog, identifiers);
        let signature =
            display_iter_next_fn_signature(query_spec, indices, rel, eqlog, identifiers);
        writedoc! {f, "
            #[link_name = \"{symbol_prefix}_{fn_name}\"]
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
        let static_name = display_weight_static_name(rel, eqlog, identifiers);
        let signature = display_weight_static_signature(rel, eqlog, identifiers);
        writedoc! {f, "
            #[link_name = \"{symbol_prefix}_{static_name}\"]
            safe {signature};
        "}
    })
}

pub fn display_table_drop_fn_name<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        write!(f, "drop_{rel_snake}_table")
    })
}

fn display_table_drop_fn_signature<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let fn_name = display_table_drop_fn_name(rel, eqlog, identifiers);
        let rel_camel = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        write!(f, "fn {fn_name}(ptr: NonNull<{rel_camel}Table>)")
    })
}

fn display_table_drop_fn<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let fn_name = display_table_drop_fn_name(rel, eqlog, identifiers);
        let signature = display_table_drop_fn_signature(rel, eqlog, identifiers);
        writedoc! {f, r#"
            #[unsafe(export_name = "{symbol_prefix}_{fn_name}")]
            pub unsafe {signature} {{
            drop(unsafe {{ Box::from_raw(ptr.as_ptr()) }});
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

pub fn display_contains_fn_name<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        write!(f, "{rel_snake}_contains")
    })
}

fn display_contains_fn_signature<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let fn_name = display_contains_fn_name(rel, eqlog, identifiers);
        let rel_camel = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        let row_type = display_rel_row_type(rel, eqlog).to_string();
        write!(
            f,
            "fn {fn_name}(table: &{rel_camel}Table, row: {row_type}) -> bool"
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
        let fn_name = display_contains_fn_name(rel, eqlog, identifiers);
        let signature = display_contains_fn_signature(rel, eqlog, identifiers);
        let indices = index_selection.get(&QuerySpec::all()).unwrap();

        let checks = indices
            .iter()
            .map(|index| {
                FmtFn(|f| {
                    let index_name = IndexName(index);
                    let order_name = OrderName(&index.order);
                    let arity_len = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog).len();
                    write!(
                        f,
                        "btree_set::contains{arity_len}(&table.index_{index_name}, &permute{order_name}(row))"
                    )
                })
            })
            .format(" || ");

        writedoc! {f, r#"
            #[unsafe(export_name = "{symbol_prefix}_{fn_name}")]
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

pub fn display_insert_fn_name<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        write!(f, "{rel_snake}_insert")
    })
}

fn display_insert_fn_signature<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let fn_name = display_insert_fn_name(rel, eqlog, identifiers);
        let rel_camel = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        let row_type = display_rel_row_type(rel, eqlog).to_string();
        write!(
            f,
            "fn {fn_name}(table: &mut {rel_camel}Table, row: {row_type}) -> bool"
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
        let fn_name = display_insert_fn_name(rel, eqlog, identifiers);
        let signature = display_insert_fn_signature(rel, eqlog, identifiers);

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
                        let arity_len = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog).len();
                        writedoc! {f, "
                            btree_set::insert{arity_len}(&mut table.index_{index_name}, permute{order}(row));"
                        }
                    } else {
                        let check = DiagonalCheck(&index.diagonals);
                        let arity_len = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog).len();
                        writedoc! {f, "
                            let check = {check};
                            if check {{
                                btree_set::insert{arity_len}(&mut table.index_{index_name}, permute{order}(row));
                            }}
                        "}
                    }
                })
            })
            .format("\n");

        let arity = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
        let arity_len = arity.len();
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
            #[unsafe(export_name = "{symbol_prefix}_{fn_name}")]
            pub extern "Rust" {signature} {{
            if btree_set::contains{arity_len}(&table.index_{primary_old}, &permute{primary_old_order}(row)) {{
            return false;
            }}
            if !btree_set::insert{arity_len}(&mut table.index_{primary_new}, permute{primary_new_order}(row)) {{
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
        let arity = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
        let arity_len = arity.len();

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
                        let arity_len = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog).len();
                        writedoc! {f, "
                            btree_set::remove{arity_len}(&mut table.index_{index_name}, &permute{order}(row));"
                        }
                    } else {
                        let check = DiagonalCheck(&index.diagonals);
                        let arity_len = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog).len();
                        writedoc! {f, "
                        let check = {check};
                        if check {{
                            btree_set::remove{arity_len}(&mut table.index_{index_name}, &permute{order}(row));
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
                        let arity_len = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog).len();
                        writedoc! {f, "
                            btree_set::remove{arity_len}(&mut table.index_{index_name}, &permute{order}(row));"
                        }
                    } else {
                        let check = DiagonalCheck(&index.diagonals);
                        let arity_len = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog).len();
                        writedoc! {f, "
                        let check = {check};
                        if check {{
                            btree_set::remove{arity_len}(&mut table.index_{index_name}, &permute{order}(row));
                        }}
                    "}
                    }
                })
            })
            .format("\n");

        let primary_new = IndexName(primary_new);
        let primary_old = IndexName(primary_old);

        writedoc! {f, "
            #[allow(unused)]
            fn remove_from_row_indices(table: &mut {rel_camel}Table, row: {row_type}) -> bool {{
                if btree_set::remove{arity_len}(&mut table.index_{primary_new}, &permute{primary_new_order}(row)) {{
                    {other_new_removes}
                    true
                }} else if btree_set::remove{arity_len}(&mut table.index_{primary_old}, &permute{primary_old_order}(row)) {{
                    {other_old_removes}
                    true
                }} else {{
                    false
                }}
            }}
        "}
    })
}

pub fn display_drain_with_element_fn_name<'a>(
    rel: Rel,
    typ: Type,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        let type_snake = display_type(typ, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        write!(f, "{rel_snake}_drain_with_element_{type_snake}")
    })
}

fn display_drain_with_element_fn_signature<'a>(
    rel: Rel,
    typ: Type,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let fn_name = display_drain_with_element_fn_name(rel, typ, eqlog, identifiers);
        let rel_camel = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        let row_type = display_rel_row_type(rel, eqlog).to_string();
        write!(
            f,
            "fn {fn_name}(table: &mut {rel_camel}Table, el: u32) -> Vec<{row_type}>"
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
                let fn_name = display_drain_with_element_fn_name(rel, typ, eqlog, identifiers);
                let signature =
                    display_drain_with_element_fn_signature(rel, typ, eqlog, identifiers);
                let type_snake = display_type(typ, eqlog, identifiers)
                    .to_string()
                    .to_case(Snake);

                writedoc! {f, r#"
            #[unsafe(export_name = "{symbol_prefix}_{fn_name}")]
            pub extern "Rust" {signature} {{
                let mut rows = table.element_index_{type_snake}.remove(&el).unwrap_or_default();

                let mut i = 0;
                while i < rows.len() {{
                    let row = rows[i];
                    if remove_from_row_indices(table, row) {{
                        i += 1;
                    }} else {{
                        rows.swap_remove(i);
                    }}
                }}

                rows
            }}
        "#}
            })
        })
        .format("\n")
}

pub fn display_move_new_to_old_fn_name<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        write!(f, "{rel_snake}_move_new_to_old")
    })
}

fn display_move_new_to_old_fn_signature<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let fn_name = display_move_new_to_old_fn_name(rel, eqlog, identifiers);
        let rel_camel = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        write!(f, "fn {fn_name}(table: &mut {rel_camel}Table)")
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
        let fn_name = display_move_new_to_old_fn_name(rel, eqlog, identifiers);
        let signature = display_move_new_to_old_fn_signature(rel, eqlog, identifiers);
        let arity = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
        let arity_len = arity.len();

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
                            btree_set::insert{arity_len}(&mut table.index_{index}, permute{index_order}(row));
                        "}
                    } else {
                        let check = DiagonalCheck(&diagonals);
                        writedoc! {f, "
                            if {check} {{
                            btree_set::insert{arity_len}(&mut table.index_{index}, permute{index_order}(row));
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
                        btree_set::clear{arity_len}(&mut table.index_{index_name});
                    "}
                })
            })
            .format("\n");

        writedoc! {f, r#"
            #[unsafe(export_name = "{symbol_prefix}_{fn_name}")]
            pub extern "Rust" {signature} {{
            let mut iter = btree_set::iter{arity_len}(&table.index_{primary_new});
            let mut row_opt = btree_set::iter_next{arity_len}(&mut iter);
            
            while let Some(row_ref) = row_opt {{
                let row = permute_inverse{primary_new_order}(*row_ref);
                {old_inserts}
                row_opt = btree_set::iter_next{arity_len}(&mut iter);
            }}

            {clear_new_indices}
            }}
        "#}
    })
}

pub fn display_has_new_data_fn_name<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        write!(f, "{rel_snake}_has_new_data")
    })
}

fn display_has_new_data_fn_signature<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let fn_name = display_has_new_data_fn_name(rel, eqlog, identifiers);
        let rel_camel = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        write!(f, "fn {fn_name}(table: &{rel_camel}Table) -> bool")
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
        let arity = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
        let arity_len = arity.len();
        let fn_name = display_has_new_data_fn_name(rel, eqlog, identifiers);
        let signature = display_has_new_data_fn_signature(rel, eqlog, identifiers);
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
            #[unsafe(export_name = "{symbol_prefix}_{fn_name}")]
            pub extern "Rust" {signature} {{
            !btree_set::is_empty{arity_len}(&table.index_{primary_new})
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

        let arity = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
        let arity_len = arity.len();

        let fields = (0..index_num)
            .map(|_| {
                FmtFn(move |f| {
                    write!(
                        f,
                        "eqlog_runtime::btree_set::BTreeSetRange{arity_len}<'a>, "
                    )
                })
            })
            .format("");

        writedoc! { f, "
            #[allow(unused)]
            pub type {rel_camel}RangeIter{index_num}<'a> = ({fields});
        "}
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

pub fn display_iter_fn_name<'a>(
    rel: Rel,
    query_spec: &'a QuerySpec,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
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

        write!(f, "iter_{rel_snake}_{age_str}{projections}{diagonals}")
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
        let fn_name = display_iter_fn_name(rel, query_spec, eqlog, identifiers);
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
                    let arity_len = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog).len();
                    writedoc! {f, "
                        let lower: {row_type} = [{fixed_args}{open_args_min}];
                        let upper: {row_type} = [{fixed_args}{open_args_max}];
                        let range{i} = btree_set::range{arity_len}(&table.index_{index_name}, std::ops::Bound::Included(lower), std::ops::Bound::Included(upper));
                    "}
                })
            })
            .format("\n");

        let range_args = (0..indices.len())
            .map(|i| FmtFn(move |f| write!(f, "range{i}, ")))
            .format("");

        writedoc! {f, r#"
            #[unsafe(export_name = "{symbol_prefix}_{fn_name}")]
            pub extern "Rust" fn {fn_name}(table: &{rel_camel}Table, {fn_args}) -> {rel_camel}RangeIter{index_num} {{
            {range_defs}
            ({range_args})
            }}
        "#}
    })
}

pub fn display_iter_next_fn_name<'a>(
    query_spec: &'a QuerySpec,
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let iter_fn = display_iter_fn_name(rel, query_spec, eqlog, identifiers);
        write!(f, "{iter_fn}_next")
    })
}

fn display_iter_next_fn_signature<'a>(
    query_spec: &'a QuerySpec,
    indices: &'a Vec<IndexSpec>,
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let fn_name = display_iter_next_fn_name(query_spec, rel, eqlog, identifiers);
        let rel_camel = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        let index_num = indices.len();
        let row_type = display_rel_row_type(rel, eqlog);
        write!(
            f,
            "fn {fn_name}(it: &mut {rel_camel}RangeIter{index_num}) -> Option<{row_type}>"
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
        let arity = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
        let arity_len = arity.len();

        let fn_name = display_iter_next_fn_name(query_spec, rel, eqlog, identifiers);
        let signature =
            display_iter_next_fn_signature(query_spec, indices, rel, eqlog, identifiers);

        let blocks = indices
            .iter()
            .enumerate()
            .map(|(i, index)| {
                FmtFn(move |f| {
                    let order_name = OrderName(index.order.as_slice());
                    writedoc! {f, "
                        if let Some(permuted_row) = btree_set::range_next{arity_len}(&mut it.{i}) {{
                            return Some(permute_inverse{order_name}(*permuted_row));
                        }}
                    "}
                })
            })
            .format("\n");

        writedoc! {f, r#"
            #[unsafe(export_name = "{symbol_prefix}_{fn_name}")]
            pub extern "Rust" {signature} {{
            {blocks}
            None
            }}
        "#}
    })
}

pub fn display_weight_static_name<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_screaming_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(UpperSnake);
        write!(f, "{rel_screaming_snake}_WEIGHT")
    })
}

fn display_weight_static_signature<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let static_name = display_weight_static_name(rel, eqlog, identifiers);
        write!(f, "static {static_name}: usize")
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
        let static_name = display_weight_static_name(rel, eqlog, identifiers);
        let signature = display_weight_static_signature(rel, eqlog, identifiers);
        let arity = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
        let tuple_weight = arity.len();
        let el_lookup_weight = tuple_weight;
        let indices_weight = indices.len() * tuple_weight;
        let weight = el_lookup_weight + indices_weight;
        writedoc! {f, r#"
            #[unsafe(export_name = "{symbol_prefix}_{static_name}")]
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
            use eqlog_runtime::btree_set;
            #[allow(unused)]
            use std::collections::BTreeMap;
            #[allow(unused)]
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
