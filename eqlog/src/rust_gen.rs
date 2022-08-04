use crate::ast::*;
use crate::flat_ast::*;
use crate::index_selection::*;
use crate::llam::*;
use crate::module::*;
use convert_case::{Case, Casing};
use indoc::{formatdoc, writedoc};
use itertools::Itertools;
use std::collections::{BTreeSet, HashMap};
use std::fmt::{self, Display, Formatter};
use std::io::{self, Write};

use Case::Snake;

fn write_imports(out: &mut impl Write) -> io::Result<()> {
    writedoc! { out, "
        use std::collections::{{BTreeSet, BTreeMap}};
        use std::fmt;
        use eqlog_util::Unification;
        use eqlog_util::tabled::{{Tabled, Table, Header, Modify, Alignment, Style, object::Segment, Extract}};
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
    let args = arity
        .iter()
        .copied()
        .format_with(", ", |sort, f| f(&format_args!("pub {sort}")));
    writedoc! {out, "
        #[allow(dead_code)]
        #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord, Tabled)]
        pub struct {relation}({args});
    "}
}

fn write_sort_fields(out: &mut impl Write, sort: &str) -> io::Result<()> {
    let sort_snake = sort.to_case(Snake);
    writedoc! {out, "
        {sort_snake}_equalities: Unification<{sort}>,
        {sort_snake}_all: BTreeSet<{sort}>,
        {sort_snake}_dirty: BTreeSet<{sort}>,
        {sort_snake}_dirty_prev: Vec<BTreeSet<{sort}>>,
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
    let element_index_fields = sorts.iter().copied().format_with("\n", |sort, f| {
        let sort_snake = sort.to_case(Snake);
        f(&format_args!(
            "    element_index_{sort_snake}: BTreeMap<{sort}, Vec<{relation}>>,"
        ))
    });

    writedoc! {out, "
        #[derive(Clone, Hash, Debug)]
        struct {relation}Table {{
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
    writedoc! {out, "
        fn permute{order_name}(t: {relation}) -> ({tuple_type_args}) {{
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
    writedoc! {out, "
        fn permute_inverse{order_name}(t: ({tuple_type_args})) -> {relation} {{
            {relation}({rel_args})
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

    writedoc! {out, "
        fn insert_dirt(&mut self, t: {relation}) -> bool {{
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

    writedoc! {out, "
        fn insert(&mut self, t: {relation}) -> bool {{
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

    writedoc! {out, "
        #[allow(dead_code)]
        fn iter_{query_name}(&self, {fn_args}) -> impl '_ + Iterator<Item = {relation}> {{
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
    let removes = indices.into_iter().format_with("\n", |index, f| {
        let index_name = IndexName(index);
        let order_name = OrderName(&index.order);
        f(&format_args!(
            "    self.index_{index_name}.remove(&Self::permute{order_name}(*t));"
        ))
    });

    // TODO: We can remove duplicates and non-canonical tuples from `ts` by deleting tuples which
    // we can't find in the master index. We try to find all t in ts in the master index to remove
    // them anyway.
    writedoc! {out, "
        #[allow(dead_code)]
        fn drain_with_element_{sort_snake}(&mut self, tm: {sort}) -> impl '_ + Iterator<Item = {relation}> {{
            let ts = match self.element_index_{sort_snake}.remove(&tm) {{
                None => Vec::new(),
                Some(tuples) => tuples,
            }};
            for t in ts.iter() {{
        {removes}
            }}
            ts.into_iter()
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

    let canonicalize_tuple =
        arity
            .iter()
            .copied()
            .enumerate()
            .format_with("\n", |(index, sort), f| {
                let sort_snake = sort.to_case(Snake);
                f(&format_args!(
                    "tuple.{index} = {sort_snake}_equalities.root(tuple.{index});"
                ))
            });

    writedoc! {out, "
        fn recall_previous_dirt(&mut self, {fn_eq_args}) {{
            let mut tmp_{index_name}_prev = Vec::new();
            std::mem::swap(&mut tmp_{index_name}_prev, &mut self.index_{index_name}_prev);

            for tuple in tmp_{index_name}_prev.into_iter().flatten() {{
                let mut tuple = Self::permute_inverse{order_name}(tuple);
                {canonicalize_tuple}
                self.insert_dirt(tuple);
            }}
        }}
    "}
}

fn write_table_impl(
    out: &mut impl Write,
    relation: &str,
    arity: &[&str],
    index_selection: &HashMap<QuerySpec, IndexSpec>,
) -> io::Result<()> {
    let indices: BTreeSet<&IndexSpec> = index_selection.values().collect();
    writedoc! {out, "
        impl {relation}Table {{
    "}?;
    write_table_new_fn(out, arity, index_selection)?;
    write_table_insert_fn(out, relation, arity, index_selection)?;
    write_table_insert_dirt_fn(out, relation, index_selection)?;
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
    writedoc! {out, "
        impl fmt::Display for {relation}Table {{
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

fn write_is_dirty_fn(out: &mut impl Write, module: &Module) -> io::Result<()> {
    let rels_dirty = module.relations().format_with(" || ", |(relation, _), f| {
        let relation_snake = relation.to_case(Snake);
        f(&format_args!("self.{relation_snake}.is_dirty()"))
    });

    let sorts_dirty = module.iter_sorts().format_with(" || ", |sort, f| {
        let sort_snake = sort.name.to_case(Snake);
        f(&format_args!("!self.{sort_snake}_dirty.is_empty()"))
    });

    writedoc! {out, "
        pub fn is_dirty(&self) -> bool {{
            self.empty_join_is_dirty ||{rels_dirty} || {sorts_dirty}
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

fn write_pub_iter_fn(out: &mut impl Write, relation: &str) -> io::Result<()> {
    let rel_snake = relation.to_case(Snake);
    writedoc! {out, "
        #[allow(dead_code)]
        pub fn iter_{rel_snake}(&self) -> impl '_ + Iterator<Item={relation}> {{
            self.{rel_snake}.iter_all()
        }}
    "}
}

fn write_pub_insert_relation(
    out: &mut impl Write,
    relation: &str,
    arity: &[&str],
) -> io::Result<()> {
    let relation_snake = relation.to_case(Snake);
    let assign_roots = arity.iter().enumerate().format_with("\n", |(i, sort), f| {
        let sort_snake = sort.to_case(Snake);
        f(&format_args!(
            "  t.{i} = self.{sort_snake}_equalities.root(t.{i});"
        ))
    });
    writedoc! {out, "
        #[allow(dead_code)]
        pub fn insert_{relation_snake}(&mut self, mut t: {relation}) {{
            {assign_roots}
            self.{relation_snake}.insert(t);
        }}
    "}
}

fn write_new_element(out: &mut impl Write, sort: &str) -> io::Result<()> {
    let sort_snake = sort.to_case(Snake);
    writedoc! {out, "
        #[allow(dead_code)]
        pub fn new_{sort_snake}(&mut self) -> {sort} {{
            let size = self.{sort_snake}_equalities.len();
            self.{sort_snake}_equalities.increase_size_to(size + 1);
            let el = {sort}::from(size as u32);
            self.{sort_snake}_dirty.insert(el);
            self.{sort_snake}_all.insert(el);
            el
        }}
    "}
}

fn write_sort_root_fn(out: &mut impl Write, sort: &str) -> io::Result<()> {
    let sort_snake = sort.to_case(Snake);
    writedoc! {out, "
        #[allow(dead_code)]
        pub fn {sort_snake}_root(&mut self, el: {sort}) -> {sort} {{
            self.{sort_snake}_equalities.root(el)
        }}
    "}
}

fn write_iter_sort_fn(out: &mut impl Write, sort: &str) -> io::Result<()> {
    let sort_snake = sort.to_case(Snake);
    writedoc! {out, "
        #[allow(dead_code)]
        pub fn iter_{sort_snake}(&mut self) -> impl '_ + Iterator<Item={sort}> {{
            self.{sort_snake}_all.iter().copied()
        }}
    "}
}

fn write_query_match_struct(
    out: &mut impl Write,
    query_action: &QueryAction,
    axiom_index: usize,
) -> io::Result<()> {
    let term_decls = query_action
        .action_inputs
        .iter()
        .format_with("\n", |(term, sort), f| {
            let tm = term.0;
            f(&format_args!("  tm{tm}: {sort},"))
        });

    writedoc! {out, "
        #[derive(Debug)]
        struct QueryMatch{axiom_index} {{
        {term_decls}
        }}
    "}
}

fn write_model_delta_struct(
    out: &mut impl Write,
    module: &Module,
    query_actions: &[QueryAction],
) -> io::Result<()> {
    let query_matches = (0..query_actions.len()).format_with("\n", |i, f| {
        f(&format_args!("    query_matches_{i}: Vec<QueryMatch{i}>,"))
    });
    let new_tuples = module.relations().format_with("\n", |(relation, _), f| {
        let relation_snake = relation.to_case(Snake);
        f(&format_args!("    new_{relation_snake}: Vec<{relation}>,"))
    });
    let new_equalities = module.iter_sorts().format_with("\n", |sort, f| {
        let sort = &sort.name;
        let sort_snake = sort.to_case(Snake);
        f(&format_args!(
            "    new_{sort_snake}_equalities: Vec<({sort}, {sort})>,"
        ))
    });
    let new_element_number = module.iter_sorts().format_with("\n", |sort, f| {
        let sort = &sort.name;
        let sort_snake = sort.to_case(Snake);
        f(&format_args!("    new_{sort_snake}_number: usize,"))
    });

    writedoc! {out, "
        #[derive(Debug)]
        struct ModelDelta {{
        {query_matches}

        {new_tuples}
        {new_equalities}
        {new_element_number}
        }}
    "}
}

fn write_model_delta_impl(
    out: &mut impl Write,
    module: &Module,
    query_actions: &[QueryAction],
) -> io::Result<()> {
    writedoc! {out, "
        impl ModelDelta {{
    "}?;

    write_model_delta_new_fn(out, module, query_actions)?;

    write_model_delta_apply_fn(out)?;
    write_model_delta_apply_new_elements_fn(out, module)?;
    write_model_delta_apply_equalities_fn(out, module)?;
    write_model_delta_apply_tuples_fn(out, module)?;

    for sort in module.iter_sorts() {
        write_model_delta_new_element_fn(out, &sort.name)?;
    }

    writedoc! {out, "
        }}
    "}?;
    Ok(())
}

fn write_model_delta_new_fn(
    out: &mut impl Write,
    module: &Module,
    query_actions: &[QueryAction],
) -> io::Result<()> {
    let query_matches = (0..query_actions.len()).format_with("\n", |i, f| {
        f(&format_args!("    query_matches_{i}: Vec::new(),"))
    });
    let new_tuples = module.relations().format_with("\n", |(relation, _), f| {
        let relation_snake = relation.to_case(Snake);
        f(&format_args!("    new_{relation_snake}: Vec::new(),"))
    });
    let new_equalities = module.iter_sorts().format_with("\n", |sort, f| {
        let sort = &sort.name;
        let sort_snake = sort.to_case(Snake);
        f(&format_args!(
            "    new_{sort_snake}_equalities: Vec::new(),"
        ))
    });
    let new_element_number = module.iter_sorts().format_with("\n", |sort, f| {
        let sort = &sort.name;
        let sort_snake = sort.to_case(Snake);
        f(&format_args!("    new_{sort_snake}_number: 0,"))
    });

    writedoc! {out, "
        fn new() -> ModelDelta {{
            ModelDelta{{
        {query_matches}
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
    module: &Module,
) -> io::Result<()> {
    let sorts = module.iter_sorts().format_with("\n", |sort, f| {
        let sort = &sort.name;
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
            self.new_{sort_snake}_number = 0;
        "})
    });
    writedoc! {out, "
        fn apply_new_elements(&mut self, model: &mut Model) {{
        {sorts}
        }}
    "}
}

fn write_model_delta_apply_equalities_fn(out: &mut impl Write, module: &Module) -> io::Result<()> {
    let sorts = module.iter_sorts().format_with("\n", |sort, f| {
        let sort = &sort.name;
        let sort_snake = sort.to_case(Snake);

        let arity_contains_sort =
            |arity: &[&str]| -> bool { arity.iter().find(|s| **s == sort).is_some() };
        let clean_rels = module
            .relations()
            .filter(|(_, arity)| arity_contains_sort(arity))
            .format_with("\n", |(relation, _), f| {
                let relation_snake = relation.to_case(Snake);
                f(&format_args! {"
                    self.new_{relation_snake}.extend(
                        model.{relation_snake}.drain_with_element_{sort_snake}(lhs)
                    );
                "})
            });

        f(&formatdoc! {"
            for (mut lhs, mut rhs) in self.new_{sort_snake}_equalities.drain(..) {{
                lhs = model.{sort_snake}_equalities.root(lhs);
                rhs = model.{sort_snake}_equalities.root(rhs);
                if lhs != rhs {{
                    model.{sort_snake}_equalities.union_roots_into(lhs, rhs);
                    model.{sort_snake}_all.remove(&lhs);
                    model.{sort_snake}_dirty.remove(&lhs);
                    {clean_rels}
                }}
            }}
        "})
    });
    writedoc! {out, "
        fn apply_equalities(&mut self, model: &mut Model) {{
        {sorts}
        }}
    "}
}

fn write_model_delta_apply_tuples_fn(out: &mut impl Write, module: &Module) -> io::Result<()> {
    let relation_tuples = module.relations().format_with("\n", |(relation, _), f| {
        let relation_snake = relation.to_case(Snake);
        f(&format_args!(
            "
                for t in self.new_{relation_snake}.drain(..) {{
                    model.insert_{relation_snake}(t);
                }}
            "
        ))
    });
    writedoc! {out, "
        fn apply_tuples(&mut self, model: &mut Model) {{
        {relation_tuples}
        }}
    "}
}

fn write_model_delta_new_element_fn(out: &mut impl Write, sort: &str) -> io::Result<()> {
    let sort_snake = sort.to_case(Snake);
    writedoc! {out, "
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
    module: &Module,
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
                    .relations()
                    .find(|(rel, _)| rel == relation)
                    .unwrap()
                    .1
                    .len();
                let query_spec = QuerySpec {
                    diagonals: diagonals.clone(),
                    projections: in_projections.keys().copied().collect(),
                    only_dirty: *only_dirty,
                };
                write!(out, "#[allow(unused_variables)]\n")?;
                write!(out, "for {}(", relation)?;
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

fn write_collect_query_matches_fn(
    out: &mut impl Write,
    module: &Module,
    query_action: &QueryAction,
    axiom_index: usize,
) -> io::Result<()> {
    writedoc! {out, "
        fn collect_query_matches_{axiom_index}(&self, delta: &mut ModelDelta) {{
    "}?;

    for query in query_action.queries.iter() {
        if query.is_empty() {
            writedoc! {out, "
                if self.empty_join_is_dirty {{
                    delta.query_matches_{axiom_index}.push(QueryMatch{axiom_index}{{}});
                }}
            "}?;
            continue;
        }

        write_query_loop_headers(out, module, query)?;
        let action_args = query_action
            .action_inputs
            .keys()
            .format_with(", ", |tm, f| {
                let tm = tm.0;
                f(&format_args!("tm{tm}"))
            });
        write!(
            out,
            "delta.query_matches_{axiom_index}.push(QueryMatch{axiom_index}{{ {action_args} }});"
        )?;
        write_query_loop_footers(out, query.len())?;
    }

    writedoc! {out, "
        }}
    "}
}

fn write_pure_query_fn(
    out: &mut impl Write,
    module: &Module,
    name: &str,
    pure_query: &PureQuery,
) -> io::Result<()> {
    let arg_list = pure_query.inputs.iter().format_with("", |(tm, sort), f| {
        let tm = tm.0;
        f(&format_args!("tm{tm}: {sort}, "))
    });

    use FlatQueryOutput::*;
    let output_type = match &pure_query.output {
        NoOutput => "bool".to_string(),
        SingleOutput(_, sort) => format!("impl Iterator<Item = {sort}>"),
        TupleOutput(tm_sorts) => {
            let sort_list = tm_sorts
                .iter()
                .format_with("", |(_, sort), f| f(&format_args!("{sort}, ")));
            format!("impl Iterator<Item = ({sort_list})>")
        }
    };

    let matches_vec_definition: &str = match &pure_query.output {
        NoOutput => "",
        SingleOutput(_, _) | TupleOutput(_) => "let mut matches = Vec::new();",
    };

    let match_found_statement = match &pure_query.output {
        NoOutput => format!("return true;"),
        SingleOutput(tm, _) => {
            let tm = tm.0;
            format!("matches.push(tm{tm});")
        }
        TupleOutput(tm_sorts) => {
            let tm_list = tm_sorts.iter().format_with("", |(tm, _), f| {
                let tm = tm.0;
                f(&format_args!("tm{}, ", tm))
            });
            format!("matches.push(({tm_list}));")
        }
    };

    let result: &str = match &pure_query.output {
        NoOutput => "false",
        SingleOutput(_, _) | TupleOutput(_) => "matches.into_iter()",
    };

    writedoc! {out, "
        #[allow(dead_code)] #[allow(unused_variables)]
        pub fn {name}(&self, {arg_list}) -> {output_type} {{
            {matches_vec_definition}
    "}?;
    assert_eq!(
        pure_query.queries.len(),
        1,
        "Pure queries with != 1 llam queries not implemented"
    );
    let query = pure_query.queries.first().unwrap();
    write_query_loop_headers(out, module, query)?;
    write!(out, "{match_found_statement}\n")?;
    write_query_loop_footers(out, query.len())?;
    writedoc! {out, "
        {result}
        }}
    "}
}

fn write_action_atom(out: &mut impl Write, module: &Module, atom: &ActionAtom) -> io::Result<()> {
    use ActionAtom::*;
    match atom {
        InsertTuple {
            relation,
            in_projections,
            out_projections,
        } => {
            let relation_snake = relation.to_case(Snake);
            let arity = module.arity(relation).unwrap();

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
                    Some({relation}({tuple_pattern_args})) => ({out_proj_args1}),
                    None => {{
                        {new_out_proj_args}
                        delta.new_{relation_snake}.push({relation}({full_tuple_args}));
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

fn write_apply_actions_fn(
    out: &mut impl Write,
    module: &Module,
    query_action: &QueryAction,
    axiom_index: usize,
) -> io::Result<()> {
    let unpack_args = query_action
        .action_inputs
        .iter()
        .format_with(", ", |(tm, _), f| {
            let tm = tm.0;
            f(&format_args!("tm{tm}"))
        });
    writedoc! {out, "
        fn apply_actions_{axiom_index}(&mut self, delta: &mut ModelDelta) {{
            let mut query_matches_{axiom_index} = Vec::new();
            std::mem::swap(&mut query_matches_{axiom_index}, &mut delta.query_matches_{axiom_index});
            for query_match in query_matches_{axiom_index} {{
                let QueryMatch{axiom_index}{{{unpack_args}}} = query_match;
    "}?;
    for atom in query_action.action.iter() {
        write_action_atom(out, module, atom)?;
    }
    writedoc! {out, "
            }}
        }}
    "}
}

fn write_drop_dirt_fn(out: &mut impl Write, module: &Module) -> io::Result<()> {
    let relations = module.relations().format_with("\n", |(relation, _), f| {
        let relation_snake = relation.to_case(Snake);
        f(&format_args!("self.{relation_snake}.drop_dirt();"))
    });
    let sorts = module.iter_sorts().format_with("\n", |sort, f| {
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

fn write_retire_dirt_fn(out: &mut impl Write, module: &Module) -> io::Result<()> {
    let relations = module.relations().format_with("\n", |(relation, _), f| {
        let relation_snake = relation.to_case(Snake);
        f(&format_args!("self.{relation_snake}.retire_dirt();"))
    });
    let sorts = module.iter_sorts().format_with("\n", |sort, f| {
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

fn write_recall_previous_dirt(out: &mut impl Write, module: &Module) -> io::Result<()> {
    let relations = module
        .relations()
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

    let sorts = module.iter_sorts().format_with("\n", |sort, f| {
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

fn write_close_fn(out: &mut impl Write, query_actions: &[QueryAction]) -> io::Result<()> {
    let is_surjective_axiom = |index: &usize| query_actions[*index].is_surjective();

    let collect_surjective_query_matches = (0..query_actions.len())
        .filter(is_surjective_axiom)
        .format_with("\n", |i, f| {
            f(&format_args!(
                "            self.collect_query_matches_{i}(&mut delta);"
            ))
        });
    let apply_surjective_axiom_actions = (0..query_actions.len())
        .filter(is_surjective_axiom)
        .format_with("\n", |i, f| {
            f(&format_args!(
                "            self.apply_actions_{i}(&mut delta);"
            ))
        });

    let collect_non_surjective_query_matches = (0..query_actions.len())
        .filter(|i| !is_surjective_axiom(i))
        .format_with("\n", |i, f| {
            f(&format_args!(
                "            self.collect_query_matches_{i}(&mut delta);"
            ))
        });
    let apply_non_surjective_axiom_actions = (0..query_actions.len())
        .filter(|i| !is_surjective_axiom(i))
        .format_with("\n", |i, f| {
            f(&format_args!("        self.apply_actions_{i}(&mut delta);"))
        });

    writedoc! {out, "
        #[allow(dead_code)]
        pub fn close(&mut self) {{
            let mut delta = ModelDelta::new();
            while self.is_dirty() {{
                loop {{
        {collect_surjective_query_matches}
            
                    self.retire_dirt();

        {apply_surjective_axiom_actions}

                    delta.apply(self);
                    if !self.is_dirty() {{
                        break;
                    }}
                }}
                self.recall_previous_dirt();
        {collect_non_surjective_query_matches}
                self.drop_dirt();
        {apply_non_surjective_axiom_actions}
                delta.apply(self);
            }}
        }}
    "}
}

fn write_new_fn(out: &mut impl Write, module: &Module) -> io::Result<()> {
    write!(out, "#[allow(dead_code)]\n")?;
    write!(out, "pub fn new() -> Self {{\n")?;
    write!(out, "Self {{\n")?;
    for sort in module.iter_sorts() {
        let sort_snake = sort.name.to_case(Snake);
        write!(out, "{sort_snake}_equalities: Unification::new(),\n")?;
        write!(out, "{}_dirty: BTreeSet::new(),\n", sort_snake)?;
        write!(out, "{sort_snake}_dirty_prev: Vec::new(),\n")?;
        write!(out, "{}_all: BTreeSet::new(),\n", sort_snake)?;
    }
    for (relation, _) in module.relations() {
        let relation_snake = relation.to_case(Snake);
        write!(out, "{relation_snake}: {relation}Table::new(),")?;
    }
    write!(out, "empty_join_is_dirty: true,\n")?;
    write!(out, "empty_join_is_dirty_prev: true,\n")?;
    write!(out, "}}\n")?;
    write!(out, "}}\n")?;
    Ok(())
}

fn write_define_fn(out: &mut impl Write, function: &Function) -> io::Result<()> {
    let Function { name, dom, cod, .. } = function;
    let function_snake = name.to_case(Snake);
    let fn_args = dom
        .iter()
        .enumerate()
        .format_with(", ", |(i, sort), f| f(&format_args!("arg{i}: {sort}")));

    let query = QuerySpec {
        projections: (0..dom.len()).collect(),
        diagonals: BTreeSet::new(),
        only_dirty: false,
    };
    let iter = IterName(&name, &query);
    let iter_args = (0..dom.len()).format_with(", ", |i, f| f(&format_args!("arg{i}")));

    let cod_index = dom.len();

    let cod_snake = cod.to_case(Snake);

    let insert_dom_args = (0..dom.len()).format_with("", |i, f| f(&format_args!("arg{i}, ")));

    writedoc! {out, "
        #[allow(dead_code)]
        pub fn define_{function_snake}(&mut self, {fn_args}) -> {cod} {{
            if let Some(t) = self.{iter}({iter_args}).next() {{
                return t.{cod_index};
            }}
            let result = self.new_{cod_snake}();
            self.insert_{function_snake}({name}({insert_dom_args}result));
            result
        }}
    "}
}

fn write_theory_struct(out: &mut impl Write, name: &str, module: &Module) -> io::Result<()> {
    write!(out, "#[derive(Debug, Clone)]\n")?;
    write!(out, "pub struct {} {{\n", name)?;
    for sort in module.iter_sorts() {
        write_sort_fields(out, &sort.name)?;
        write!(out, "\n")?;
    }

    for (relation, _) in module.relations() {
        let relation_snake = relation.to_case(Snake);
        write!(out, "  {relation_snake}: {relation}Table,")?;
    }

    write!(out, "empty_join_is_dirty: bool,\n")?;
    write!(out, "empty_join_is_dirty_prev: bool,\n")?;
    write!(out, "}}\n")?;
    write!(out, "type Model = {name};")?;
    Ok(())
}

fn write_theory_impl(
    out: &mut impl Write,
    name: &str,
    module: &Module,
    query_actions: &[QueryAction],
    pure_queries: &[(String, PureQuery)],
) -> io::Result<()> {
    write!(out, "impl {} {{\n", name)?;
    for sort in module.iter_sorts() {
        write_new_element(out, &sort.name)?;
        write_iter_sort_fn(out, &sort.name)?;
        write_sort_root_fn(out, &sort.name)?;
        write!(out, "\n")?;
    }
    for (rel, arity) in module.relations() {
        write_pub_iter_fn(out, rel)?;
        write_pub_insert_relation(out, rel, &arity)?;
        write!(out, "\n")?;
    }

    write_new_fn(out, module)?;
    write!(out, "\n")?;

    write_is_dirty_fn(out, module)?;
    write!(out, "\n")?;

    for (i, query_action) in query_actions.iter().enumerate() {
        write_collect_query_matches_fn(out, module, query_action, i)?;
        write_apply_actions_fn(out, module, query_action, i)?;
    }
    for function in module.iter_functions() {
        write_define_fn(out, function)?;
    }
    for (name, pure_query) in pure_queries.iter() {
        write_pure_query_fn(out, module, name, pure_query)?;
    }

    write_drop_dirt_fn(out, module)?;
    write_retire_dirt_fn(out, module)?;
    write_recall_previous_dirt(out, module)?;
    write_close_fn(out, query_actions)?;

    write!(out, "}}\n")?;
    Ok(())
}

fn write_theory_display_impl(out: &mut impl Write, name: &str, module: &Module) -> io::Result<()> {
    let els = module.iter_sorts().format_with("", |sort, f| {
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
    let rels = module.relations().format_with("", |(rel, _), f| {
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
    module: &Module,
    query_actions: &[QueryAction],
    pure_queries: &[(String, PureQuery)],
    index_selection: &IndexSelection,
) -> io::Result<()> {
    write_imports(out)?;
    write!(out, "\n")?;

    for sort in module.iter_sorts() {
        write_sort_struct(out, &sort.name)?;
        write_sort_impl(out, &sort.name)?;
    }
    write!(out, "\n")?;

    for (rel, arity) in module.relations() {
        write_relation_struct(out, rel, &arity)?;
        let index = index_selection.get(rel).unwrap();
        write_table_struct(out, rel, &arity, index)?;
        write_table_impl(out, rel, &arity, index)?;
        write_table_display_impl(out, rel)?;
    }
    write!(out, "\n")?;

    for (i, qa) in query_actions.iter().enumerate() {
        write_query_match_struct(out, qa, i)?;
        write!(out, "\n")?;
    }

    write_model_delta_struct(out, module, query_actions)?;
    write_theory_struct(out, name, module)?;

    write_model_delta_impl(out, module, query_actions)?;
    write!(out, "\n")?;

    write_theory_impl(out, name, module, query_actions, pure_queries)?;
    write_theory_display_impl(out, name, module)?;

    Ok(())
}
