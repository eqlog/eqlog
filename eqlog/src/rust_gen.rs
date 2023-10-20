use crate::eqlog_util::*;
use crate::flat_ast::*;
use crate::index_selection::*;
use crate::llam::*;
use crate::module::*;
use convert_case::{Case, Casing};
use eqlog_eqlog::*;
use indoc::{formatdoc, writedoc};
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{self, Display, Formatter};
use std::io::{self, Write};

use Case::{Snake, UpperCamel};

fn write_imports(out: &mut impl Write) -> io::Result<()> {
    writedoc! { out, "
        #[allow(unused)]
        use std::collections::{{BTreeSet, BTreeMap}};
        use std::fmt;
        #[allow(unused)]
        use eqlog_runtime::Unification;
        use eqlog_runtime::tabled::{{Tabled, Table, Header, Modify, Alignment, Style, object::Segment, Extract}};
        use std::ops::Bound;
    "}
}

// #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
// pub struct SortName(pub u32);
fn write_sort_struct(out: &mut impl Write, sort: &str) -> io::Result<()> {
    writedoc! {out, "
        #[allow(dead_code)]
        #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
        pub struct {sort}(pub u32);
    "}
}

fn write_sort_impl(out: &mut impl Write, sort: &str) -> io::Result<()> {
    writedoc! {out, "
        impl Into<u32> for {sort} {{ fn into(self) -> u32 {{ self.0 }} }}
        impl From<u32> for {sort} {{ fn from(x: u32) -> Self {{ {sort}(x) }} }}
        impl fmt::Display for {sort} {{
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {{
                write!(f, \"{{:?}}\", self)
            }}
        }}
    "}
}

// #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
// pub struct RelationName(pub SortOne, pub SortTwo, ..., pub SortN);
fn write_relation_struct(out: &mut impl Write, relation: &str, arity: &[&str]) -> io::Result<()> {
    let relation_camel = relation.to_case(UpperCamel);
    let args = arity
        .iter()
        .copied()
        .format_with(", ", |sort, f| f(&format_args!("pub {sort}")));
    writedoc! {out, "
        #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord, Tabled)]
        struct {relation_camel}({args});
    "}
}

fn write_sort_fields(out: &mut impl Write, sort: &str) -> io::Result<()> {
    let sort_snake = sort.to_case(Snake);
    writedoc! {out, "
        {sort_snake}_equalities: Unification<{sort}>,
        {sort_snake}_all: BTreeSet<{sort}>,
        {sort_snake}_dirty: BTreeSet<{sort}>,
        {sort_snake}_dirty_prev: Vec<BTreeSet<{sort}>>,
        {sort_snake}_weights: Vec<usize>,
    "}
}

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

struct IndexName<'a>(&'a IndexSpec);

impl<'a> Display for IndexName<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let index = self.0;
        let dirty_str = if index.only_dirty { "dirty" } else { "all" };
        write!(f, "{dirty_str}")?;
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

fn write_table_struct(
    out: &mut impl Write,
    relation: &str,
    arity: &[&str],
    index_selection: &HashMap<QuerySpec, IndexSpec>,
) -> io::Result<()> {
    let indices: BTreeSet<&IndexSpec> = index_selection.values().collect();
    let tuple_type_args = (0..arity.len()).format_with("", |_, f| f(&format_args!("u32, ")));
    let tuple_type = format!("({tuple_type_args})");

    let index_fields = indices.iter().copied().format_with("\n", |index, f| {
        let index_name = IndexName(index);
        f(&format_args!(
            "    index_{index_name}: BTreeSet<{tuple_type}>,"
        ))
    });

    let dirty_index = index_selection.get(&QuerySpec::all_dirty()).unwrap();
    let dirty_index_name = IndexName(dirty_index);
    let prev_dirty_field = format!("index_{dirty_index_name}_prev: Vec<BTreeSet<{tuple_type}>>,");

    let sorts: BTreeSet<&str> = arity.iter().copied().collect();
    let relation_camel = relation.to_case(UpperCamel);
    let element_index_fields = sorts.iter().copied().format_with("\n", |sort, f| {
        let sort_snake = sort.to_case(Snake);
        f(&format_args!(
            "    element_index_{sort_snake}: BTreeMap<{sort}, Vec<{relation_camel}>>,"
        ))
    });

    writedoc! {out, "
        #[derive(Clone, Hash, Debug)]
        struct {relation_camel}Table {{
        {index_fields}

        {prev_dirty_field}

        {element_index_fields}
        }}
    "}
}

fn write_table_new_fn(
    out: &mut impl Write,
    arity: &[&str],
    index_selection: &HashMap<QuerySpec, IndexSpec>,
) -> io::Result<()> {
    let indices: BTreeSet<&IndexSpec> = index_selection.values().collect();
    let index_inits = indices.iter().copied().format_with("\n", |index, f| {
        let index_name = IndexName(index);
        f(&format_args!(
            "        index_{index_name}: BTreeSet::new(),"
        ))
    });

    let dirty_index = index_selection.get(&QuerySpec::all_dirty()).unwrap();
    let dirty_index_name = IndexName(dirty_index);
    let prev_dirty_init = format!("index_{dirty_index_name}_prev: Vec::new(),");

    let sorts: BTreeSet<&str> = arity.iter().copied().collect();
    let element_index_inits = sorts.iter().copied().format_with("\n", |sort, f| {
        let sort_snake = sort.to_case(Snake);
        f(&format_args!(
            "    element_index_{sort_snake}: BTreeMap::new(),"
        ))
    });
    writedoc! {out, "
        fn new() -> Self {{
            Self {{
        {index_inits}
        {prev_dirty_init}
        {element_index_inits}
            }}
        }}
    "}
}

fn write_table_permute_fn(
    out: &mut impl Write,
    relation: &str,
    arity: &[&str],
    order: &[usize],
) -> io::Result<()> {
    let tuple_type_args = (0..arity.len()).format_with("", |_, f| f(&format_args!("u32, ")));
    let order_name = OrderName(order);
    let tuple_args = order
        .iter()
        .format_with("", |i, f| f(&format_args!("t.{i}.into(), ")));
    let relation_camel = relation.to_case(UpperCamel);
    writedoc! {out, "
        #[allow(unused)]
        fn permute{order_name}(t: {relation_camel}) -> ({tuple_type_args}) {{
            ({tuple_args})
        }}
    "}
}

fn write_table_permute_inverse_fn(
    out: &mut impl Write,
    relation: &str,
    arity: &[&str],
    order: &[usize],
) -> io::Result<()> {
    let tuple_type_args = (0..arity.len()).format_with("", |_, f| f(&format_args!("u32, ")));
    let order_name = OrderName(order);
    let rel_args = (0..order.len()).format_with(", ", |i, f| {
        let sort = arity[i];
        let j = order.iter().copied().position(|j| j == i).unwrap();
        f(&format_args!("{sort}::from(t.{j})"))
    });
    let relation_camel = relation.to_case(UpperCamel);
    writedoc! {out, "
        #[allow(unused)]
        fn permute_inverse{order_name}(t: ({tuple_type_args})) -> {relation_camel} {{
            {relation_camel}({rel_args})
        }}
    "}
}

struct DiagonalCheck<'a>(&'a BTreeSet<BTreeSet<usize>>);
impl<'a> Display for DiagonalCheck<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let diags = &self.0;
        let all_clauses = diags.iter().format_with(" && ", |diag, f| {
            let diag_clauses = diag
                .iter()
                .zip(diag.iter().skip(1))
                .format_with(" && ", |(prev, next), f| {
                    f(&format_args!("t.{prev} == t.{next}"))
                });
            f(&format_args!("{diag_clauses}"))
        });
        write!(f, "{all_clauses}")
    }
}

// TODO: This and write_table_insert_fn are very similar. Refactor?
fn write_table_insert_dirt_fn(
    out: &mut impl Write,
    relation: &str,
    index_selection: &HashMap<QuerySpec, IndexSpec>,
) -> io::Result<()> {
    let master_index = index_selection.get(&QuerySpec::all_dirty()).unwrap();
    let master = IndexName(&master_index);
    let master_order = OrderName(&master_index.order);

    let indices: BTreeSet<&IndexSpec> = index_selection.values().collect();
    let slave_inserts = indices
        .into_iter()
        .filter(|index| index.only_dirty && *index != master_index)
        .format_with("\n", |index, f| {
            let index_name = IndexName(index);
            let order = OrderName(&index.order);
            if index.diagonals.is_empty() {
                f(&format_args!(
                    "self.index_{index_name}.insert(Self::permute{order}(t));"
                ))
            } else {
                let check = DiagonalCheck(&index.diagonals);
                f(&format_args! {"
                    if {check} {{
                        self.index_{index_name}.insert(Self::permute{order}(t));
                    }}
                "})
            }
        });

    let relation_camel = relation.to_case(UpperCamel);
    writedoc! {out, "
        fn insert_dirt(&mut self, t: {relation_camel}) -> bool {{
            if self.index_{master}.insert(Self::permute{master_order}(t)) {{
        {slave_inserts}
                true
            }} else {{
                false
            }}
        }}
    "}
}

fn write_table_insert_fn(
    out: &mut impl Write,
    relation: &str,
    arity: &[&str],
    index_selection: &HashMap<QuerySpec, IndexSpec>,
) -> io::Result<()> {
    let master_index = index_selection.get(&QuerySpec::all()).unwrap();
    let master = IndexName(&master_index);
    let master_order = OrderName(&master_index.order);

    let indices: BTreeSet<&IndexSpec> = index_selection.values().collect();
    let slave_inserts = indices
        .into_iter()
        .filter(|index| *index != master_index)
        .format_with("\n", |index, f| {
            let index_name = IndexName(index);
            let order = OrderName(&index.order);
            if index.diagonals.is_empty() {
                f(&format_args!(
                    "self.index_{index_name}.insert(Self::permute{order}(t));"
                ))
            } else {
                let check = DiagonalCheck(&index.diagonals);
                f(&format_args! {"
                    if {check} {{
                        self.index_{index_name}.insert(Self::permute{order}(t));
                    }}
                "})
            }
        });

    let element_inserts = arity
        .iter()
        .copied()
        .enumerate()
        .format_with("\n", |(i, sort), f| {
            let sort_snake = sort.to_case(Snake);
            // TODO: Use try_insert here once it stabilizes.
            f(&format_args! {"
            match self.element_index_{sort_snake}.get_mut(&t.{i}) {{
                Some(tuple_vec) => tuple_vec.push(t),
                None => {{ self.element_index_{sort_snake}.insert(t.{i}, vec![t]); }},
            }};
        "})
        });

    let relation_camel = relation.to_case(UpperCamel);
    // TODO: Why is this not used sometimes?
    writedoc! {out, "
        #[allow(dead_code)]
        fn insert(&mut self, t: {relation_camel}) -> bool {{
            if self.index_{master}.insert(Self::permute{master_order}(t)) {{
        {slave_inserts}
        {element_inserts}
                true
            }} else {{
                false
            }}
        }}
    "}
}

struct QueryName<'a>(&'a QuerySpec);

impl<'a> Display for QueryName<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let query = self.0;
        let dirty_str = if query.only_dirty { "dirty" } else { "all" };
        write!(f, "{dirty_str}")?;
        for i in query.projections.iter() {
            write!(f, "_{i}")?;
        }
        for diag in query.diagonals.iter() {
            write!(f, "_diagonal")?;
            for d in diag.iter() {
                write!(f, "_{d}")?;
            }
        }
        Ok(())
    }
}

fn write_table_iter_fn(
    out: &mut impl Write,
    relation: &str,
    arity: &[&str],
    query: &QuerySpec,
    index: &IndexSpec,
) -> io::Result<()> {
    assert!(index.can_serve(query));
    let query_name = QueryName(query);
    let index_name = IndexName(index);
    let order_name = OrderName(&index.order);

    // (arg3: Mor, arg5: Obj, ...)
    let fn_args = query.projections.iter().copied().format_with(", ", |i, f| {
        let sort = arity[i];
        f(&format_args!("arg{i}: {sort}"))
    });

    let unalias_args = query
        .projections
        .iter()
        .copied()
        .format_with("\n", |i, f| f(&format_args!("    let arg{i} = arg{i}.0;")));

    let fixed_arg_len = query.projections.len();
    let open_arg_len = arity.len() - query.projections.len();

    let fixed_args = || {
        index.order[..fixed_arg_len]
            .iter()
            .format_with("", |i, f| f(&format_args!("arg{i}, ")))
    };
    let fixed_args_min = fixed_args();
    let fixed_args_max = fixed_args();

    let open_args_min = (0..open_arg_len).format_with("", |_, f| f(&format_args!("u32::MIN, ")));
    let open_args_max = (0..open_arg_len).format_with("", |_, f| f(&format_args!("u32::MAX, ")));

    let relation_camel = relation.to_case(UpperCamel);
    writedoc! {out, "
        #[allow(dead_code)]
        fn iter_{query_name}(&self, {fn_args}) -> impl '_ + Iterator<Item = {relation_camel}> {{
        {unalias_args}
            let min = ({fixed_args_min}{open_args_min});
            let max = ({fixed_args_max}{open_args_max});
            self.index_{index_name}
                .range((Bound::Included(&min), Bound::Included(&max)))
                .copied()
                .map(Self::permute_inverse{order_name})
        }}
    "}
}

fn write_table_contains_fn(
    out: &mut impl Write,
    relation: &str,
    index_selection: &HashMap<QuerySpec, IndexSpec>,
) -> io::Result<()> {
    let master = index_selection.get(&QuerySpec::all()).unwrap();
    let master_name = IndexName(master);
    let order_name = OrderName(&master.order);
    let relation_camel = relation.to_case(UpperCamel);
    writedoc! {out, "
        #[allow(dead_code)]
        fn contains(&self, t: {relation_camel}) -> bool {{
            self.index_{master_name}.contains(&Self::permute{order_name}(t))
        }}
    "}
}

fn write_table_is_dirty_fn(
    out: &mut impl Write,
    index_selection: &HashMap<QuerySpec, IndexSpec>,
) -> io::Result<()> {
    let master_dirty = IndexName(index_selection.get(&QuerySpec::all_dirty()).unwrap());

    writedoc! {out, "
        fn is_dirty(&self) -> bool {{
            !self.index_{master_dirty}.is_empty()
        }}
    "}
}

fn write_table_drop_dirt_fn(
    out: &mut impl Write,
    index_selection: &HashMap<QuerySpec, IndexSpec>,
) -> io::Result<()> {
    let indices: BTreeSet<&IndexSpec> = index_selection.values().collect();
    let clears = indices
        .iter()
        .copied()
        .filter(|index| index.only_dirty)
        .format_with("\n", |index, f| {
            let index_name = IndexName(index);
            f(&format_args!("    self.index_{index_name}.clear();"))
        });
    writedoc! {out, "
        fn drop_dirt(&mut self) {{
            {clears}
        }}
    "}
}

fn write_table_retire_dirt_fn(
    out: &mut impl Write,
    index_selection: &HashMap<QuerySpec, IndexSpec>,
) -> io::Result<()> {
    let indices: BTreeSet<&IndexSpec> = index_selection.values().collect();
    let dirty_master = index_selection.get(&QuerySpec::all_dirty()).unwrap();
    let clears = indices
        .iter()
        .copied()
        .filter(|index| index.only_dirty && *index != dirty_master)
        .format_with("\n", |index, f| {
            let index_name = IndexName(index);
            f(&format_args!("    self.index_{index_name}.clear();"))
        });
    let dirty_master_name = IndexName(dirty_master);
    writedoc! {out, "
        fn retire_dirt(&mut self) {{
            {clears}
            let mut tmp_{dirty_master_name} = BTreeSet::new();
            std::mem::swap(&mut tmp_{dirty_master_name}, &mut self.index_{dirty_master_name});
            self.index_{dirty_master_name}_prev.push(tmp_{dirty_master_name});
        }}
    "}
}

fn write_table_drain_with_element(
    out: &mut impl Write,
    relation: &str,
    index_selection: &HashMap<QuerySpec, IndexSpec>,
    sort: &str,
) -> io::Result<()> {
    let sort_snake = sort.to_case(Snake);
    let indices: BTreeSet<&IndexSpec> = index_selection.values().collect();
    let master_index = index_selection.get(&QuerySpec::all()).unwrap();
    let master_index_name = IndexName(master_index);
    let master_order_name = OrderName(&master_index.order);
    let slave_removes = indices
        .into_iter()
        .filter(|index| index != &master_index)
        .format_with("\n", |index, f| {
            let index_name = IndexName(index);
            let order_name = OrderName(&index.order);
            f(&format_args!(
                "self.index_{index_name}.remove(&Self::permute{order_name}(*t));"
            ))
        });

    let relation_camel = relation.to_case(UpperCamel);
    writedoc! {out, "
        #[allow(dead_code)]
        fn drain_with_element_{sort_snake}(&mut self, tm: {sort}) -> impl '_ + Iterator<Item = {relation_camel}> {{
            let ts = match self.element_index_{sort_snake}.remove(&tm) {{
                None => Vec::new(),
                Some(tuples) => tuples,
            }};

            ts.into_iter()
                .filter(|t| {{
                    if self.index_{master_index_name}.remove(&Self::permute{master_order_name}(*t)) {{
                        {slave_removes}
                        true
                    }} else {{
                        false
                    }}
                }})
        }}
    "}
}

fn write_table_recall_previous_dirt(
    out: &mut impl Write,
    arity: &[&str],
    index_selection: &HashMap<QuerySpec, IndexSpec>,
) -> io::Result<()> {
    let sorts = arity.iter().copied().collect::<BTreeSet<&str>>();
    let fn_eq_args = sorts.iter().copied().format_with("", |sort, f| {
        let sort_snake = sort.to_case(Snake);
        f(&format_args!(
            "{sort_snake}_equalities: &mut Unification<{sort}>,"
        ))
    });
    let index = index_selection.get(&QuerySpec::all_dirty()).unwrap();
    let index_name = IndexName(index);
    let order_name = OrderName(&index.order);

    let is_canonical_checks =
        arity
            .iter()
            .copied()
            .enumerate()
            .format_with("", |(index, sort), f| {
                let sort_snake = sort.to_case(Snake);
                f(&format_args!(
                    "&& tuple.{index} == {sort_snake}_equalities.root(tuple.{index})"
                ))
            });

    writedoc! {out, "
        fn recall_previous_dirt(&mut self, {fn_eq_args}) {{
            let mut tmp_{index_name}_prev = Vec::new();
            std::mem::swap(&mut tmp_{index_name}_prev, &mut self.index_{index_name}_prev);

            for tuple in tmp_{index_name}_prev.into_iter().flatten() {{
                #[allow(unused_mut)]
                let mut tuple = Self::permute_inverse{order_name}(tuple);
                if true {is_canonical_checks} {{
                    self.insert_dirt(tuple);
                }}
            }}
        }}
    "}
}

fn write_table_weight(
    out: &mut impl Write,
    arity: &[&str],
    index_selection: &HashMap<QuerySpec, IndexSpec>,
) -> io::Result<()> {
    let indices: BTreeSet<&IndexSpec> = index_selection.values().collect();
    let tuple_weight = arity.len();
    let el_lookup_weight = tuple_weight;
    let indices_weight = indices.len() * tuple_weight;
    let weight = el_lookup_weight + indices_weight;
    writedoc! {out, "
        #[allow(unused)]
        const WEIGHT: usize = {weight};
    "}
}

fn write_table_impl(
    out: &mut impl Write,
    relation: &str,
    arity: &[&str],
    index_selection: &HashMap<QuerySpec, IndexSpec>,
) -> io::Result<()> {
    let indices: BTreeSet<&IndexSpec> = index_selection.values().collect();
    let relation_camel = relation.to_case(UpperCamel);
    writedoc! {out, "
        impl {relation_camel}Table {{
    "}?;
    write_table_weight(out, arity, index_selection)?;
    write_table_new_fn(out, arity, index_selection)?;
    write_table_insert_fn(out, relation, arity, index_selection)?;
    write_table_insert_dirt_fn(out, relation, index_selection)?;
    write_table_contains_fn(out, relation, index_selection)?;
    write_table_drop_dirt_fn(out, index_selection)?;
    write_table_retire_dirt_fn(out, index_selection)?;
    write_table_is_dirty_fn(out, index_selection)?;

    let index_orders: BTreeSet<&[usize]> =
        indices.iter().map(|index| index.order.as_slice()).collect();
    for order in index_orders {
        write_table_permute_fn(out, relation, arity, order)?;
        write_table_permute_inverse_fn(out, relation, arity, order)?;
    }
    for (query, index) in index_selection.iter() {
        write_table_iter_fn(out, relation, arity, query, index)?;
    }
    for sort in arity.iter().copied().collect::<BTreeSet<&str>>() {
        write_table_drain_with_element(out, relation, index_selection, sort)?;
    }
    write_table_recall_previous_dirt(out, arity, index_selection)?;
    writedoc! {out, "
        }}
    "}
}

fn write_table_display_impl(out: &mut impl Write, relation: &str) -> io::Result<()> {
    let relation_camel = relation.to_case(UpperCamel);
    writedoc! {out, "
        impl fmt::Display for {relation_camel}Table {{
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {{
                Table::new(self.iter_all())
                    .with(Extract::segment(1.., ..))
                    .with(Header(\"{relation}\"))
                    .with(Modify::new(Segment::all()).with(Alignment::center()))
                    .with(
                        Style::modern()
                            .top_intersection('─')
                            .header_intersection('┬')
                    )
                    .fmt(f)
            }}
        }}
    "}
}

fn write_is_dirty_fn(out: &mut impl Write, module: &ModuleWrapper) -> io::Result<()> {
    let rels_dirty = module
        .symbols
        .iter_rels()
        .format_with("", |(relation, _), f| {
            let relation_snake = relation.to_case(Snake);
            f(&format_args!(" || self.{relation_snake}.is_dirty()"))
        });

    let sorts_dirty = module.symbols.iter_types().format_with("", |sort, f| {
        let sort_snake = sort.name.to_case(Snake);
        f(&format_args!(" || !self.{sort_snake}_dirty.is_empty()"))
    });

    writedoc! {out, "
        fn is_dirty(&self) -> bool {{
            self.empty_join_is_dirty {rels_dirty} {sorts_dirty}
        }}
    "}
}

struct IterName<'a>(&'a str, &'a QuerySpec);

impl<'a> Display for IterName<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let IterName(relation, query_spec) = self;
        let relation_snake = relation.to_case(Snake);
        let dirty_str = if query_spec.only_dirty {
            "dirty"
        } else {
            "all"
        };
        write!(f, "{relation_snake}.iter_{dirty_str}")?;
        for p in query_spec.projections.iter() {
            write!(f, "_{p}")?;
        }
        for diag in query_spec.diagonals.iter() {
            write!(f, "_diagonal")?;
            for d in diag.iter() {
                write!(f, "_{d}")?;
            }
        }
        Ok(())
    }
}

fn write_pub_predicate_holds_fn(
    out: &mut impl Write,
    relation: &str,
    arity: &[&str],
) -> io::Result<()> {
    let relation_snake = relation.to_case(Snake);
    let rel_fn_args = arity
        .iter()
        .copied()
        .enumerate()
        .format_with("", |(i, s), f| f(&format_args!(", mut arg{i}: {s}")));

    let canonicalize = arity
        .iter()
        .copied()
        .enumerate()
        .format_with("\n", |(i, s), f| {
            let sort_snake = s.to_case(Snake);
            f(&format_args!("arg{i} = self.root_{sort_snake}(arg{i});"))
        });

    let rel_args0 = (0..arity.len()).format_with(", ", |i, f| f(&format_args!("arg{i}")));
    let rel_args1 = rel_args0.clone();
    let relation_camel = relation.to_case(UpperCamel);
    writedoc! {out, "
        /// Returns `true` if `{relation}({rel_args0})` holds.
        #[allow(dead_code)]
        pub fn {relation_snake}(&self{rel_fn_args}) -> bool {{
            {canonicalize}
            self.{relation_snake}.contains({relation_camel}({rel_args1}))
        }}
    "}
}

fn write_pub_function_eval_fn(
    out: &mut impl Write,
    relation: &str,
    arity: &[&str],
) -> io::Result<()> {
    let relation_snake = relation.to_case(Snake);
    let dom = &arity[..(arity.len() - 1)];
    let cod_index = dom.len();
    let cod = arity[cod_index];

    let rel_fn_args = dom
        .iter()
        .copied()
        .enumerate()
        .format_with("", |(i, s), f| f(&format_args!(", mut arg{i}: {s}")));

    let canonicalize = dom
        .iter()
        .copied()
        .enumerate()
        .format_with("\n", |(i, s), f| {
            let sort_snake = s.to_case(Snake);
            f(&format_args!("arg{i} = self.root_{sort_snake}(arg{i});"))
        });

    let query = QuerySpec {
        projections: (0..dom.len()).collect(),
        diagonals: BTreeSet::new(),
        only_dirty: false,
    };
    let iter = IterName(relation, &query);
    let args0 = (0..dom.len()).format_with(", ", |i, f| f(&format_args!("arg{i}")));
    let args1 = args0.clone();

    writedoc! {out, "
        /// Evaluates `{relation}({args0})`.
        #[allow(dead_code)]
        pub fn {relation_snake}(&self{rel_fn_args}) -> Option<{cod}> {{
            {canonicalize}
            self.{iter}({args1}).next().map(|t| t.{cod_index})
        }}
    "}
}

fn write_pub_iter_fn(
    out: &mut impl Write,
    relation: &str,
    arity: &[&str],
    is_function: bool,
) -> io::Result<()> {
    let rel_snake = relation.to_case(Snake);
    let rel_type = if arity.len() == 1 {
        arity.first().unwrap().to_string()
    } else {
        let args = arity
            .iter()
            .copied()
            .format_with(", ", |s, f| f(&format_args!("{}", s)));
        format!("({args})")
    };

    let tuple_unpack = match arity.len() {
        0 => "|_| ()".to_string(),
        1 => "|t| t.0".to_string(),
        n => {
            let args = (0..n).format_with(", ", |i, f| f(&format_args!("t.{i}")));
            format!("|t| ({args})")
        }
    };

    let docstring = match (is_function, arity.len()) {
        (false, 0) => todo!("Shouldn't generate an iter_...() function for truth values."),
        (false, 1) => {
            formatdoc! {"
                /// Returns an iterator over elements satisfying the `{relation}` predicate.
            "}
        }
        (false, n) => {
            debug_assert!(n > 0);
            formatdoc! {"
                /// Returns an iterator over tuples of elements satisfying the `{relation}` predicate.
            "}
        }
        (true, 0) => panic!("Functions cannot have empty arity"),
        (true, 1) => {
            formatdoc! {"
                /// Returns an iterator over `{relation}` constants.
                /// The iterator may yield more than one element if the model is not closed.
            "}
        }
        (true, n) => {
            debug_assert!(n > 1);
            formatdoc! {"
                /// Returns an iterator over tuples in the graph of the `{relation}` function.
                /// The relation yielded by the iterator need not be functional if the model is not closed.
            "}
        }
    };

    writedoc! {out, "
        {docstring}
        #[allow(dead_code)]
        pub fn iter_{rel_snake}(&self) -> impl '_ + Iterator<Item={rel_type}> {{
            self.{rel_snake}.iter_all().map({tuple_unpack})
        }}
    "}
}

fn write_pub_insert_relation(
    out: &mut impl Write,
    relation: &str,
    arity: &[&str],
    is_function: bool,
) -> io::Result<()> {
    let relation_snake = relation.to_case(Snake);
    let rel_fn_args = arity
        .iter()
        .copied()
        .enumerate()
        .format_with("", |(i, s), f| {
            if is_function && i == arity.len() - 1 {
                f(&format_args!(", result: {s}"))
            } else {
                f(&format_args!(", arg{i}: {s}"))
            }
        });
    let rel_args = (0..arity.len()).format_with("", |i, f| {
        if is_function && i == arity.len() - 1 {
            f(&format_args!("result,"))
        } else {
            f(&format_args!("arg{i},"))
        }
    });

    let docstring = if is_function {
        let dom = &arity[0..arity.len() - 1];
        let args = (0..dom.len()).format_with(", ", |i, f| f(&format_args!("arg{i}")));
        formatdoc! {"
                /// Makes the equation `{relation}({args}) = result` hold.
            "}
    } else {
        let args = (0..arity.len()).format_with(", ", |i, f| f(&format_args!("arg{i}")));
        formatdoc! {"
                /// Makes `{relation}({args})` hold.
            "}
    };
    let relation_camel = relation.to_case(UpperCamel);
    writedoc! {out, "
        {docstring}
        #[allow(dead_code)]
        pub fn insert_{relation_snake}(&mut self {rel_fn_args}) {{
            self.delta.as_mut().unwrap().new_{relation_snake}.push({relation_camel}({rel_args}));
        }}
    "}
}

fn write_new_element(out: &mut impl Write, sort: &str) -> io::Result<()> {
    let sort_snake = sort.to_case(Snake);
    writedoc! {out, "
        /// Adjoins a new element of sort `{sort}`.
        #[allow(dead_code)]
        pub fn new_{sort_snake}(&mut self) -> {sort} {{
            let mut delta_opt = None;
            std::mem::swap(&mut delta_opt, &mut self.delta);
            let mut delta = delta_opt.unwrap();

            let el = delta.new_{sort_snake}(self);

            self.delta = Some(delta);
            el
        }}
    "}
}

fn write_equate_elements(out: &mut impl Write, sort: &str) -> io::Result<()> {
    let sort_snake = sort.to_case(Snake);
    writedoc! {out, "
        /// Enforces the equality `lhs = rhs`.
        #[allow(dead_code)]
        pub fn equate_{sort_snake}(&mut self, lhs: {sort}, rhs: {sort}) {{
            self.delta.as_mut().unwrap().new_{sort_snake}_equalities.push((lhs, rhs));
        }}
    "}
}

fn write_root_fn(out: &mut impl Write, sort: &str) -> io::Result<()> {
    let sort_snake = sort.to_case(Snake);
    writedoc! {out, "
        /// Returns the canonical representative of the equivalence class of `el`.
        #[allow(dead_code)]
        pub fn root_{sort_snake}(&self, el: {sort}) -> {sort} {{
            if el.0 as usize >= self.{sort_snake}_equalities.len() {{
                el
            }} else {{
                self.{sort_snake}_equalities.root_const(el)
            }}
        }}
    "}
}

fn write_are_equal_fn(out: &mut impl Write, sort: &str) -> io::Result<()> {
    let sort_snake = sort.to_case(Snake);
    writedoc! {out, "
        /// Returns `true` if `lhs` and `rhs` are in the same equivalence class.
        #[allow(dead_code)]
        pub fn are_equal_{sort_snake}(&self, lhs: {sort}, rhs: {sort}) -> bool {{
            self.root_{sort_snake}(lhs) == self.root_{sort_snake}(rhs)
        }}
    "}
}

fn write_iter_sort_fn(out: &mut impl Write, sort: &str) -> io::Result<()> {
    let sort_snake = sort.to_case(Snake);
    writedoc! {out, "
        /// Returns and iterator over elements of sort `{sort}`.
        /// The iterator yields canonical representatives only.
        #[allow(dead_code)]
        pub fn iter_{sort_snake}(&self) -> impl '_ + Iterator<Item={sort}> {{
            self.{sort_snake}_all.iter().copied()
        }}
    "}
}

fn write_model_delta_struct(
    out: &mut impl Write,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> io::Result<()> {
    let new_tuples = iter_relation_arities(eqlog, identifiers).format_with("\n", |(name, _), f| {
        let name_snake = name.to_case(Snake);
        let name_camel = name.to_case(UpperCamel);
        f(&format_args!("    new_{name_snake}: Vec<{name_camel}>,"))
    });

    let new_equalities = eqlog.iter_type_decl().format_with("\n", |(_, ident), f| {
        let name = identifiers.get(&ident).unwrap().as_str();
        let name_snake = name.to_case(Snake);
        f(&format_args!(
            "    new_{name_snake}_equalities: Vec<({name}, {name})>,"
        ))
    });
    let new_element_number = eqlog.iter_type_decl().format_with("\n", |(_, ident), f| {
        let name = identifiers.get(&ident).unwrap().as_str();
        let name_snake = name.to_case(Snake);
        f(&format_args!("    new_{name_snake}_number: usize,"))
    });

    writedoc! {out, "
        #[derive(Debug, Clone)]
        struct ModelDelta {{
        {new_tuples}
        {new_equalities}
        {new_element_number}
        }}
    "}
}

fn write_model_delta_impl(
    out: &mut impl Write,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> io::Result<()> {
    writedoc! {out, "
        impl ModelDelta {{
    "}?;

    write_model_delta_new_fn(out, eqlog, identifiers)?;

    write_model_delta_apply_fn(out)?;
    write_model_delta_apply_new_elements_fn(out, eqlog, identifiers)?;
    write_model_delta_apply_equalities_fn(out, eqlog, identifiers)?;
    write_model_delta_apply_tuples_fn(out, eqlog, identifiers)?;

    for type_name in iter_types(eqlog, identifiers) {
        write_model_delta_new_element_fn(out, type_name)?;
    }

    writedoc! {out, "
        }}
    "}?;
    Ok(())
}

fn write_model_delta_new_fn(
    out: &mut impl Write,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> io::Result<()> {
    let new_tuples =
        iter_relation_arities(eqlog, identifiers).format_with("\n", |(relation, _), f| {
            let relation_snake = relation.to_case(Snake);
            f(&format_args!("    new_{relation_snake}: Vec::new(),"))
        });
    let new_equalities = iter_types(eqlog, identifiers).format_with("\n", |sort, f| {
        let sort_snake = sort.to_case(Snake);
        f(&format_args!(
            "    new_{sort_snake}_equalities: Vec::new(),"
        ))
    });
    let new_element_number = iter_types(eqlog, identifiers).format_with("\n", |sort, f| {
        let sort_snake = sort.to_case(Snake);
        f(&format_args!("    new_{sort_snake}_number: 0,"))
    });

    writedoc! {out, "
        fn new() -> ModelDelta {{
            ModelDelta{{
        {new_tuples}
        {new_equalities}
        {new_element_number}
            }}
        }}
    "}
}

fn write_model_delta_apply_fn(out: &mut impl Write) -> io::Result<()> {
    writedoc! {out, "
        fn apply(&mut self, model: &mut Model) {{
            self.apply_new_elements(model);
            self.apply_equalities(model);
            self.apply_tuples(model);
        }}
    "}
}

fn write_model_delta_apply_new_elements_fn(
    out: &mut impl Write,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> io::Result<()> {
    let sorts = iter_types(eqlog, identifiers).format_with("\n", |sort, f| {
        let sort_snake = sort.to_case(Snake);
        f(&formatdoc! {"
            let old_{sort_snake}_number = model.{sort_snake}_equalities.len();
            let new_{sort_snake}_number = old_{sort_snake}_number + self.new_{sort_snake}_number;
            model.{sort_snake}_equalities.increase_size_to(new_{sort_snake}_number);
            for i in old_{sort_snake}_number .. new_{sort_snake}_number {{
                let el = {sort}::from(i as u32);
                model.{sort_snake}_dirty.insert(el);
                model.{sort_snake}_all.insert(el);
            }}

            model.{sort_snake}_weights.resize(new_{sort_snake}_number, 0);

            self.new_{sort_snake}_number = 0;
        "})
    });
    writedoc! {out, "
        #[allow(unused)]
        fn apply_new_elements(&mut self, model: &mut Model) {{
        {sorts}
        }}
    "}
}

fn write_model_delta_apply_equalities_fn(
    out: &mut impl Write,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> io::Result<()> {
    let sorts = iter_types(eqlog, identifiers).format_with("\n", |sort, f| {
        let sort_snake = sort.to_case(Snake);

        let arity_contains_sort =
            |arity: &[&str]| -> bool { arity.iter().find(|s| **s == sort).is_some() };
        let clean_rels = iter_relation_arities(eqlog, identifiers)
            .filter(|(_, arity)| arity_contains_sort(arity))
            .format_with("\n", |(relation, arity), f| {
                let relation_snake = relation.to_case(Snake);
                let relation_camel = relation.to_case(UpperCamel);
                let update_weights =
                    arity
                        .iter()
                        .copied()
                        .enumerate()
                        .format_with("\n", |(i, s), f| {
                            let sort_snake = s.to_case(Snake);
                            f(&formatdoc! {"
                                let weight{i} =
                                    model.{sort_snake}_weights
                                    .get_mut(t.{i}.0 as usize)
                                    .unwrap(); 
                                *weight{i} -= {relation_camel}Table::WEIGHT;
                            "})
                        });
                f(&format_args! {"
                    self.new_{relation_snake}.extend(
                        model.{relation_snake}
                        .drain_with_element_{sort_snake}(child)
                        .inspect(|t| {{
                            {update_weights}
                        }})
                    );
                "})
            });

        f(&formatdoc! {"
            for (mut lhs, mut rhs) in self.new_{sort_snake}_equalities.drain(..) {{
                lhs = model.{sort_snake}_equalities.root(lhs);
                rhs = model.{sort_snake}_equalities.root(rhs);
                if lhs == rhs {{
                    continue;
                }}

                let lhs_weight = model.{sort_snake}_weights[lhs.0 as usize];
                let rhs_weight = model.{sort_snake}_weights[rhs.0 as usize];
                let (root, child) =
                    if lhs_weight >= rhs_weight {{
                        (lhs, rhs)
                    }} else {{
                        (rhs, lhs)
                    }};

                model.{sort_snake}_equalities.union_roots_into(child, root);
                model.{sort_snake}_all.remove(&child);
                model.{sort_snake}_dirty.remove(&child);
                {clean_rels}
            }}
        "})
    });
    writedoc! {out, "
        #[allow(unused)]
        fn apply_equalities(&mut self, model: &mut Model) {{
        {sorts}
        }}
    "}
}

fn write_model_delta_apply_tuples_fn(
    out: &mut impl Write,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> io::Result<()> {
    let relations =
        iter_relation_arities(eqlog, identifiers).format_with("\n", |(relation, arity), f| {
            let relation_snake = relation.to_case(Snake);
            let relation_camel = relation.to_case(UpperCamel);
            let canonicalize = arity.iter().enumerate().format_with("\n", |(i, sort), f| {
                let sort_snake = sort.to_case(Snake);
                f(&format_args!(
                    "t.{i} = model.{sort_snake}_equalities.root(t.{i});"
                ))
            });
            let update_weights = arity.iter().enumerate().format_with("\n", |(i, sort), f| {
                let sort_snake = sort.to_case(Snake);
                f(&format_args!(
                    "model.{sort_snake}_weights[t.{i}.0 as usize] += {relation_camel}Table::WEIGHT;"
                ))
            });
            f(&formatdoc! {"
                #[allow(unused_mut)]
                for mut t in self.new_{relation_snake}.drain(..) {{
                    {canonicalize}
                    if model.{relation_snake}.insert(t) {{
                        {update_weights}
                    }}
                }}
            "})
        });
    writedoc! {out, "
        fn apply_tuples(&mut self, model: &mut Model) {{
            {relations}
        }}
    "}
}

fn write_model_delta_new_element_fn(out: &mut impl Write, sort: &str) -> io::Result<()> {
    let sort_snake = sort.to_case(Snake);
    writedoc! {out, "
        #[allow(dead_code)]
        fn new_{sort_snake}(&mut self, model: &Model) -> {sort} {{
            let id: usize = model.{sort_snake}_equalities.len() + self.new_{sort_snake}_number;
            assert!(id <= (u32::MAX as usize));
            self.new_{sort_snake}_number += 1;
            {sort}::from(id as u32)
        }}
    "}
}

fn write_query_loop_headers<'a>(
    out: &mut impl Write,
    module: &ModuleWrapper,
    query: impl IntoIterator<Item = &'a QueryAtom>,
) -> io::Result<()> {
    for atom in query.into_iter() {
        use QueryAtom::*;
        match atom {
            Equal(lhs, rhs) => {
                write!(out, "if tm{} == tm{} {{\n", lhs.0, rhs.0)?;
            }
            Relation {
                relation,
                diagonals,
                in_projections,
                out_projections,
                only_dirty,
                quantifier,
            } => {
                assert_eq!(
                    *quantifier,
                    Quantifier::All,
                    "Only Quantifier::All is implemented"
                );
                let arity_len = module
                    .symbols
                    .iter_rels()
                    .find(|(rel, _)| rel == relation)
                    .unwrap()
                    .1
                    .len();
                let query_spec = QuerySpec {
                    diagonals: diagonals.clone(),
                    projections: in_projections.keys().copied().collect(),
                    only_dirty: *only_dirty,
                };
                let relation_camel = relation.to_case(UpperCamel);
                write!(out, "#[allow(unused_variables)]\n")?;
                write!(out, "for {relation_camel}(")?;
                for i in 0..arity_len {
                    if let Some(tm) = out_projections.get(&i) {
                        if let Some(diag) = diagonals.iter().find(|diag| diag.contains(&i)) {
                            if *diag.iter().next().unwrap() == i {
                                write!(out, "tm{}", tm.0)?;
                            } else {
                                write!(out, "_")?;
                            }
                        } else {
                            write!(out, "tm{}", tm.0)?;
                        }
                    } else {
                        write!(out, "_")?;
                    }
                    write!(out, ", ")?;
                }
                write!(out, ") in self.")?;
                let iter_name = IterName(relation, &query_spec);
                write!(out, "{iter_name}")?;
                write!(out, "(")?;
                for tm in in_projections.values().copied() {
                    write!(out, "tm{}, ", tm.0)?;
                }
                write!(out, ") {{\n")?;
            }
            Sort {
                sort,
                result,
                only_dirty,
            } => {
                let dirty_str = if *only_dirty { "dirty" } else { "all" };
                let result = result.0;
                let sort_snake = sort.to_case(Snake);
                writedoc! {out, "
                    #[allow(unused_variables)]
                    for tm{result} in self.{sort_snake}_{dirty_str}.iter().copied() {{
                "}?;
            }
        }
    }
    Ok(())
}

fn write_query_loop_footers(out: &mut impl Write, query_len: usize) -> io::Result<()> {
    for _ in 0..query_len {
        write!(out, "}}\n")?;
    }
    Ok(())
}

fn write_query_and_record_fn(
    out: &mut impl Write,
    module: &ModuleWrapper,
    query_action: &QueryAction,
    axiom_index: usize,
) -> io::Result<()> {
    writedoc! {out, "
        fn query_and_record_{axiom_index}(&self, delta: &mut ModelDelta) {{
    "}?;

    for query in query_action.queries.iter() {
        if query.is_empty() {
            writedoc! {out, "
                if self.empty_join_is_dirty {{
                    self.record_action_{axiom_index}(delta);
                }}
            "}?;
            continue;
        }

        write_query_loop_headers(out, module, query)?;
        let action_args = query_action
            .action_inputs
            .iter()
            .format_with(", ", |tm, f| {
                let tm = tm.0;
                f(&format_args!("tm{tm}"))
            });
        write!(
            out,
            "self.record_action_{axiom_index}(delta, {action_args});"
        )?;
        write_query_loop_footers(out, query.len())?;
    }

    writedoc! {out, "
        }}
    "}
}

fn write_action_atom(
    out: &mut impl Write,
    module: &ModuleWrapper,
    atom: &ActionAtom,
) -> io::Result<()> {
    use ActionAtom::*;
    match atom {
        InsertTuple {
            relation,
            in_projections,
            out_projections,
        } => {
            let relation_snake = relation.to_case(Snake);
            let relation_camel = relation.to_case(UpperCamel);
            let arity = module.symbols.get_arity(relation).unwrap();

            let query_spec = QuerySpec {
                projections: in_projections.keys().copied().collect(),
                diagonals: BTreeSet::new(),
                only_dirty: false,
            };
            let iter_name = IterName(relation, &query_spec);

            let in_proj_args = in_projections.values().format_with(", ", |tm, f| {
                let tm = tm.0;
                f(&format_args!("tm{tm}"))
            });
            let out_proj_args0 = out_projections.values().format_with("", |tm, f| {
                let tm = tm.0;
                f(&format_args!("tm{tm}, "))
            });
            let out_proj_args1 = out_proj_args0.clone();
            let out_proj_args2 = out_proj_args0.clone();
            let tuple_pattern_args = (0..arity.len()).format_with(", ", |index, f| {
                if let Some(tm) = out_projections.get(&index) {
                    let tm = tm.0;
                    f(&format_args!("tm{tm}"))
                } else {
                    f(&format_args!("_"))
                }
            });
            let new_out_proj_args = out_projections.iter().format_with("\n", |(index, tm), f| {
                let tm = tm.0;
                let sort_snake = arity[*index].to_case(Snake);
                f(&format_args!("let tm{tm} = delta.new_{sort_snake}(self);"))
            });
            let full_tuple_args = (0..arity.len()).format_with(",", |index, f| {
                let tm = if let Some(tm) = in_projections.get(&index) {
                    tm.0
                } else {
                    out_projections.get(&index).unwrap().0
                };
                f(&format_args!("tm{tm}"))
            });
            writedoc! {out, "
                let existing_row = self.{iter_name}({in_proj_args}).next();
                #[allow(unused_variables)]
                let ({out_proj_args0}) = match existing_row {{
                    Some({relation_camel}({tuple_pattern_args})) => ({out_proj_args1}),
                    None => {{
                        {new_out_proj_args}
                        delta.new_{relation_snake}.push({relation_camel}({full_tuple_args}));
                        ({out_proj_args2})
                    }},
                }};
            "}
        }
        Equate { sort, lhs, rhs } => {
            let lhs = lhs.0;
            let rhs = rhs.0;
            let sort_snake = sort.to_case(Snake);
            writedoc! {out, "
                if tm{lhs} != tm{rhs} {{
                    delta.new_{sort_snake}_equalities.push((tm{lhs}, tm{rhs}));
                }}
            "}
        }
    }
}

fn write_record_action_fn(
    out: &mut impl Write,
    module: &ModuleWrapper,
    sorts: &BTreeMap<FlatTerm, String>,
    action_inputs: &BTreeSet<FlatTerm>,
    action: &[ActionAtom],
    axiom_index: usize,
) -> io::Result<()> {
    let args = action_inputs.iter().format_with("", |tm, f| {
        let sort = sorts.get(tm).unwrap();
        let tm = tm.0;
        f(&format_args!("tm{tm}: {sort}, "))
    });

    writedoc! {out, "
        fn record_action_{axiom_index}(&self, delta: &mut ModelDelta, {args}) {{
    "}?;
    for atom in action.iter() {
        write_action_atom(out, module, atom)?;
    }
    writedoc! {out, "
        }}
    "}
}

fn write_drop_dirt_fn(out: &mut impl Write, module: &ModuleWrapper) -> io::Result<()> {
    let relations = module
        .symbols
        .iter_rels()
        .format_with("\n", |(relation, _), f| {
            let relation_snake = relation.to_case(Snake);
            f(&format_args!("self.{relation_snake}.drop_dirt();"))
        });
    let sorts = module.symbols.iter_types().format_with("\n", |sort, f| {
        let sort_snake = sort.name.to_case(Snake);
        f(&format_args!("self.{sort_snake}_dirty.clear();"))
    });

    writedoc! {out, "
        fn drop_dirt(&mut self) {{
            self.empty_join_is_dirty = false;

        {relations}

        {sorts}
        }}
    "}
}

fn write_retire_dirt_fn(out: &mut impl Write, module: &ModuleWrapper) -> io::Result<()> {
    let relations = module
        .symbols
        .iter_rels()
        .format_with("\n", |(relation, _), f| {
            let relation_snake = relation.to_case(Snake);
            f(&format_args!("self.{relation_snake}.retire_dirt();"))
        });
    let sorts = module.symbols.iter_types().format_with("\n", |sort, f| {
        let sort_snake = sort.name.to_case(Snake);
        f(&formatdoc! {"
            let mut {sort_snake}_dirty_tmp = BTreeSet::new();
            std::mem::swap(&mut {sort_snake}_dirty_tmp, &mut self.{sort_snake}_dirty);
            self.{sort_snake}_dirty_prev.push({sort_snake}_dirty_tmp);
        "})
    });
    writedoc! {out, "
        fn retire_dirt(&mut self) {{
            self.empty_join_is_dirty = false;

        {relations}

        {sorts}
        }}
    "}
}

fn write_recall_previous_dirt(out: &mut impl Write, module: &ModuleWrapper) -> io::Result<()> {
    let relations = module
        .symbols
        .iter_rels()
        .format_with("\n", |(relation, arity), f| {
            let relation_snake = relation.to_case(Snake);
            let sorts: BTreeSet<&str> = arity.iter().copied().collect();
            let args = sorts.into_iter().format_with(", ", |sort, f| {
                let sort_snake = sort.to_case(Snake);
                f(&format_args!("&mut self.{sort_snake}_equalities"))
            });
            f(&format_args!(
                "self.{relation_snake}.recall_previous_dirt({args});"
            ))
        });

    let sorts = module.symbols.iter_types().format_with("\n", |sort, f| {
        let sort_snake = sort.name.to_case(Snake);
        f(&formatdoc! {"
                let mut {sort_snake}_dirty_prev_tmp = Vec::new();
                std::mem::swap(&mut {sort_snake}_dirty_prev_tmp, &mut self.{sort_snake}_dirty_prev);
                self.{sort_snake}_dirty =
                    {sort_snake}_dirty_prev_tmp
                    .into_iter()
                    .flatten()
                    .filter(|el| self.{sort_snake}_equalities.root(*el) == *el)
                    .collect();
            "})
    });
    writedoc! {out, "
        fn recall_previous_dirt(&mut self) {{
            debug_assert!(!self.is_dirty());

            {relations}

            {sorts}

            self.empty_join_is_dirty = self.empty_join_is_dirty_prev;
            self.empty_join_is_dirty_prev = false;
        }}
    "}
}

fn write_close_until_fn(out: &mut impl Write, query_actions: &[QueryAction]) -> io::Result<()> {
    let is_surjective_axiom = |index: &usize| query_actions[*index].is_surjective();

    let surjective_axioms = (0..query_actions.len())
        .filter(is_surjective_axiom)
        .format_with("\n", |i, f| {
            f(&format_args!("self.query_and_record_{i}(&mut delta);"))
        });

    let non_surjective_axioms = (0..query_actions.len())
        .filter(|i| !is_surjective_axiom(i))
        .format_with("\n", |i, f| {
            f(&format_args!("self.query_and_record_{i}(&mut delta);"))
        });

    writedoc! {out, "
        /// Closes the model under all axioms until `condition` is satisfied.
        /// Depending on the axioms and `condition`, this may run indefinitely.
        /// Returns `true` if the `condition` eventually holds.
        /// Returns `false` if the model could be closed under all axioms but `condition` still does not hold.
        #[allow(dead_code)]
        pub fn close_until(&mut self, condition: impl Fn(&Self) -> bool) -> bool
        {{
            let mut delta_opt = None;
            std::mem::swap(&mut delta_opt, &mut self.delta);
            let mut delta = delta_opt.unwrap();

            delta.apply(self);
            if condition(self) {{
                self.delta = Some(delta);
                return true;
            }}

            while self.is_dirty() {{
                loop {{
        {surjective_axioms}
            
                    self.retire_dirt();
                    delta.apply(self);

                    if condition(self) {{
                        self.delta = Some(delta);
                        return true;
                    }}
                    if !self.is_dirty() {{
                        break;
                    }}
                }}

                self.recall_previous_dirt();
        {non_surjective_axioms}
                self.drop_dirt();
                delta.apply(self);
                if condition(self) {{
                    self.delta = Some(delta);
                    return true;
                }}
            }}

            self.delta = Some(delta);
            return false;
        }}
    "}
}

fn write_close_fn(out: &mut impl Write) -> io::Result<()> {
    writedoc! {out, "
        /// Closes the model under all axioms.
        /// Depending on the axioms and the model, this may run indefinitely.
        #[allow(dead_code)]
        pub fn close(&mut self) {{
            self.close_until(|_: &Self| false);
        }}
    "}
}

fn write_new_fn(
    out: &mut impl Write,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> io::Result<()> {
    write!(out, "/// Creates an empty model.\n")?;
    write!(out, "#[allow(dead_code)]\n")?;
    write!(out, "pub fn new() -> Self {{\n")?;
    write!(out, "Self {{\n")?;
    for sort in iter_types(eqlog, identifiers) {
        let sort_snake = sort.to_case(Snake);
        write!(out, "{sort_snake}_equalities: Unification::new(),\n")?;
        write!(out, "{}_dirty: BTreeSet::new(),\n", sort_snake)?;
        write!(out, "{sort_snake}_dirty_prev: Vec::new(),\n")?;
        write!(out, "{sort_snake}_weights: Vec::new(),\n")?;
        write!(out, "{}_all: BTreeSet::new(),\n", sort_snake)?;
    }
    for (relation, _) in iter_relation_arities(eqlog, identifiers) {
        let relation_snake = relation.to_case(Snake);
        let relation_camel = relation.to_case(UpperCamel);
        write!(out, "{relation_snake}: {relation_camel}Table::new(),")?;
    }
    write!(out, "empty_join_is_dirty: true,\n")?;
    write!(out, "empty_join_is_dirty_prev: true,\n")?;
    write!(out, "delta: Some(Box::new(ModelDelta::new())),\n")?;
    write!(out, "}}\n")?;
    write!(out, "}}\n")?;
    Ok(())
}

fn write_define_fn(out: &mut impl Write, name: &str, arity: &[&str]) -> io::Result<()> {
    assert!(
        arity.len() >= 1,
        "Arity of function should have at least return type"
    );
    let arg_types = &arity[0..arity.len() - 1];
    let result_type = arity.last().unwrap();

    let function_snake = name.to_case(Snake);

    let fn_args = arg_types
        .iter()
        .enumerate()
        .format_with(", ", |(i, typ), f| f(&format_args!("mut arg{i}: {typ}")));

    let query = QuerySpec {
        projections: (0..arg_types.len()).collect(),
        diagonals: BTreeSet::new(),
        only_dirty: false,
    };
    let iter = IterName(&name, &query);
    let iter_args = (0..arg_types.len()).format_with(", ", |i, f| f(&format_args!("arg{i}")));

    let cod_index = arg_types.len();

    let cod_snake = result_type.to_case(Snake);

    let insert_dom_args = (0..arg_types.len()).format_with("", |i, f| f(&format_args!("arg{i}, ")));

    let canonicalize = arg_types
        .iter()
        .enumerate()
        .format_with("\n", |(i, arg_type), f| {
            let sort_snake = arg_type.to_case(Snake);
            f(&format_args!("arg{i} = self.root_{sort_snake}(arg{i});"))
        });

    let args = iter_args.clone();
    writedoc! {out, "
        /// Enforces that `{name}({args})` is defined, adjoining a new element if necessary.
        #[allow(dead_code)]
        pub fn define_{function_snake}(&mut self, {fn_args}) -> {result_type} {{
            {canonicalize}
            if let Some(t) = self.{iter}({iter_args}).next() {{
                return t.{cod_index};
            }}
            let result = self.new_{cod_snake}();
            self.insert_{function_snake}({insert_dom_args}result);
            result
        }}
    "}
}

fn write_theory_struct(
    out: &mut impl Write,
    name: &str,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> io::Result<()> {
    write!(out, "/// A model of the `{name}` theory.\n")?;
    write!(out, "#[derive(Debug, Clone)]\n")?;
    write!(out, "pub struct {} {{\n", name)?;
    for (_, type_ident) in eqlog.iter_type_decl() {
        let type_name = identifiers.get(&type_ident).unwrap().as_str();
        write_sort_fields(out, type_name)?;
        write!(out, "\n")?;
    }

    for (relation, _) in iter_relation_arities(eqlog, identifiers) {
        let relation_snake = relation.to_case(Snake);
        let relation_camel = relation.to_case(UpperCamel);
        write!(out, "  {relation_snake}: {relation_camel}Table,")?;
    }

    write!(out, "empty_join_is_dirty: bool,\n")?;
    write!(out, "empty_join_is_dirty_prev: bool,\n")?;
    write!(out, "delta: Option<Box<ModelDelta>>,\n")?;
    write!(out, "}}\n")?;
    write!(out, "type Model = {name};")?;
    Ok(())
}

fn write_theory_impl(
    out: &mut impl Write,
    name: &str,
    module: &ModuleWrapper,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
    query_actions: &[QueryAction],
) -> io::Result<()> {
    write!(out, "impl {} {{\n", name)?;

    write_new_fn(out, eqlog, identifiers)?;
    write!(out, "\n")?;

    write_close_fn(out)?;
    write_close_until_fn(out, query_actions)?;

    for type_name in iter_types(eqlog, identifiers) {
        write_new_element(out, type_name)?;
        write_equate_elements(out, type_name)?;
        write_iter_sort_fn(out, type_name)?;
        write_root_fn(out, type_name)?;
        write_are_equal_fn(out, type_name)?;
        write!(out, "\n")?;
    }

    for (func_name, arity) in iter_func_arities(eqlog, identifiers) {
        write_pub_function_eval_fn(out, func_name, &arity)?;
        write_define_fn(out, func_name, &arity)?;
        write_pub_iter_fn(out, func_name, &arity, true)?;
        write_pub_insert_relation(out, func_name, &arity, true)?;
        write!(out, "\n")?;
    }

    for (pred, arity) in iter_pred_arities(eqlog, identifiers) {
        write_pub_predicate_holds_fn(out, pred, &arity)?;
        if arity.len() > 0 {
            write_pub_iter_fn(out, pred, &arity, false)?;
        }
        write_pub_insert_relation(out, &pred, &arity, false)?;
        write!(out, "\n")?;
    }

    write_is_dirty_fn(out, module)?;
    write!(out, "\n")?;

    for (i, query_action) in query_actions.iter().enumerate() {
        write_record_action_fn(
            out,
            module,
            &query_action.sorts,
            &query_action.action_inputs,
            &query_action.action,
            i,
        )?;
        write_query_and_record_fn(out, module, query_action, i)?;
    }

    write_drop_dirt_fn(out, module)?;
    write_retire_dirt_fn(out, module)?;
    write_recall_previous_dirt(out, module)?;

    write!(out, "}}\n")?;
    Ok(())
}

fn write_theory_display_impl(
    out: &mut impl Write,
    name: &str,
    module: &ModuleWrapper,
) -> io::Result<()> {
    let els = module.symbols.iter_types().format_with("", |sort, f| {
        let sort_camel = &sort.name;
        let sort_snake = sort.name.to_case(Snake);
        let modify_table = formatdoc! {"
            with(Header(\"{sort_camel}\"))
            .with(Modify::new(Segment::all())
            .with(Alignment::center()))
            .with(
                Style::modern()
                    .top_intersection('─')
                    .header_intersection('┬')
            )
        "};
        f(&format_args!(
            "self.{sort_snake}_equalities.class_table().{modify_table}.fmt(f)?;"
        ))
    });
    let rels = module.symbols.iter_rels().format_with("", |(rel, _), f| {
        let rel_snake = rel.to_case(Snake);
        f(&format_args!("self.{rel_snake}.fmt(f)?;"))
    });

    writedoc! {out, "
        impl fmt::Display for {name} {{
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {{
                {els}
                {rels}
                Ok(())
            }}
        }}
    "}
}

pub fn write_module(
    out: &mut impl Write,
    name: &str,
    module: &ModuleWrapper,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
    query_actions: &[QueryAction],
    index_selection: &IndexSelection,
) -> io::Result<()> {
    write_imports(out)?;
    write!(out, "\n")?;

    for (_, ident) in eqlog.iter_type_decl() {
        let name = identifiers.get(&ident).unwrap().as_str();
        write_sort_struct(out, name)?;
        write_sort_impl(out, name)?;
    }
    write!(out, "\n")?;

    for (rel, arity) in iter_relation_arities(eqlog, identifiers) {
        write_relation_struct(out, rel, &arity)?;
        let index = index_selection.get(rel).unwrap();
        write_table_struct(out, rel, &arity, index)?;
        write_table_impl(out, rel, &arity, index)?;
        write_table_display_impl(out, rel)?;
    }
    write!(out, "\n")?;

    write_model_delta_struct(out, eqlog, identifiers)?;
    write_theory_struct(out, name, eqlog, identifiers)?;

    write_model_delta_impl(out, eqlog, identifiers)?;
    write!(out, "\n")?;

    write_theory_impl(out, name, module, eqlog, identifiers, query_actions)?;
    write_theory_display_impl(out, name, module)?;

    Ok(())
}
