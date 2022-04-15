use crate::ast::*;
use crate::flat_ast::FlatTerm;
use crate::index_selection::*;
use crate::query_action::*;
use crate::signature::Signature;
use convert_case::{Case, Casing};
use indoc::writedoc;
use itertools::Itertools;
use std::collections::{BTreeSet, HashMap};
use std::fmt::{self, Display, Formatter};
use std::io::{self, Write};
use std::iter::once;

use Case::Snake;

fn write_imports(out: &mut impl Write) -> io::Result<()> {
    writedoc! { out, "
        use std::collections::{{BTreeSet, BTreeMap}};
        use eqlog_util::Unification;
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
        #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
        pub struct {relation}({args});
    "}
}

fn write_sort_fields(out: &mut impl Write, sort: &str) -> io::Result<()> {
    let sort_snake = sort.to_case(Snake);
    writedoc! {out, "
        {sort_snake}_equalities: Unification<{sort}>,
        {sort_snake}_all: BTreeSet<{sort}>,
        {sort_snake}_dirty: BTreeSet<{sort}>,
    "}
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
enum TupleAge {
    All,
    Dirty,
}

impl Display for TupleAge {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            TupleAge::All => write!(f, "all"),
            TupleAge::Dirty => write!(f, "dirty"),
        }
    }
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

struct IndexName<'a>(TupleAge, &'a IndexSpec);

impl<'a> Display for IndexName<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let age = self.0;
        let index = self.1;
        write!(f, "{age}")?;
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

    let index_fields = indices
        .iter()
        .copied()
        .cartesian_product([TupleAge::All, TupleAge::Dirty])
        .format_with("\n", |(index, age), f| {
            let index_name = IndexName(age, index);
            let tuple_type_args =
                (0..arity.len()).format_with("", |_, f| f(&format_args!("u32, ")));
            f(&format_args!(
                "    index_{index_name}: BTreeSet<({tuple_type_args})>,"
            ))
        });

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
    let index_inits = indices
        .iter()
        .cartesian_product([TupleAge::All, TupleAge::Dirty])
        .format_with("\n", |(index, age), f| {
            let index_name = IndexName(age, index);
            f(&format_args!(
                "        index_{index_name}: BTreeSet::new(),"
            ))
        });

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
    let rel_args = order.iter().copied().format_with(", ", |i, f| {
        let sort = arity[i];
        f(&format_args!("{sort}::from(t.{i})"))
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

fn write_table_insert_fn(
    out: &mut impl Write,
    relation: &str,
    arity: &[&str],
    index_selection: &HashMap<QuerySpec, IndexSpec>,
) -> io::Result<()> {
    let master_index = index_selection.get(&QuerySpec::new()).unwrap();
    let master = IndexName(TupleAge::All, &master_index);
    let master_order = OrderName(&master_index.order);

    let indices: BTreeSet<&IndexSpec> = index_selection.values().collect();
    let slave_inserts = indices
        .into_iter()
        .cartesian_product([TupleAge::All, TupleAge::Dirty])
        .filter(|(index, age)| (*index, *age) != (master_index, TupleAge::All))
        .format_with("\n", |(index, age), f| {
            let index_name = IndexName(age, index);
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

struct QueryName<'a>(TupleAge, &'a QuerySpec);

impl<'a> Display for QueryName<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let age = self.0;
        let query = self.1;
        write!(f, "{age}")?;
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
    age: TupleAge,
    index: &IndexSpec,
) -> io::Result<()> {
    assert!(index.can_serve(query));
    let query_name = QueryName(age, query);
    let index_name = IndexName(age, index);
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
    let master_index = index_selection.get(&QuerySpec::new()).unwrap();
    let master = IndexName(TupleAge::Dirty, master_index);
    writedoc! {out, "
        fn is_dirty(&self) -> bool {{
            !self.index_{master}.is_empty()
        }}
    "}
}

fn write_table_clear_dirt_fn(
    out: &mut impl Write,
    index_selection: &HashMap<QuerySpec, IndexSpec>,
) -> io::Result<()> {
    let indices: BTreeSet<&IndexSpec> = index_selection.values().collect();
    let clears = indices.iter().copied().format_with("\n", |index, f| {
        let index_name = IndexName(TupleAge::Dirty, index);
        f(&format_args!("    self.index_{index_name}.clear();"))
    });
    writedoc! {out, "
        fn drop_dirt(&mut self) {{
            {clears}
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
    let removes = indices
        .into_iter()
        .cartesian_product([TupleAge::All, TupleAge::Dirty])
        .format_with("\n", |(index, age), f| {
            let index_name = IndexName(age, index);
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
    write_table_clear_dirt_fn(out, index_selection)?;
    write_table_is_dirty_fn(out, index_selection)?;

    let index_orders: BTreeSet<&[usize]> =
        indices.iter().map(|index| index.order.as_slice()).collect();
    for order in index_orders {
        write_table_permute_fn(out, relation, arity, order)?;
        write_table_permute_inverse_fn(out, relation, arity, order)?;
    }
    for (query, index) in index_selection.iter() {
        for age in [TupleAge::All, TupleAge::Dirty] {
            write_table_iter_fn(out, relation, arity, query, age, index)?;
        }
    }
    for sort in arity.iter().copied().collect::<BTreeSet<&str>>() {
        write_table_drain_with_element(out, relation, index_selection, sort)?;
    }
    writedoc! {out, "
        }}
    "}
}

fn write_is_dirty_fn(out: &mut impl Write, signature: &Signature) -> io::Result<()> {
    let rels_dirty = signature
        .relations()
        .format_with(" || ", |(relation, _), f| {
            let relation_snake = relation.to_case(Snake);
            f(&format_args!("self.{relation_snake}.is_dirty()"))
        });

    let sorts_dirty = signature.iter_sorts().format_with(" || ", |sort, f| {
        let sort_snake = sort.name.to_case(Snake);
        f(&format_args!("!self.{sort_snake}_dirty.is_empty()"))
    });

    writedoc! {out, "
        pub fn is_dirty(&self) -> bool {{
            self.empty_join_is_dirty ||{rels_dirty} || {sorts_dirty}
        }}
    "}
}

struct IterName<'a>(&'a str, TupleAge, &'a QuerySpec);

impl<'a> Display for IterName<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let relation_snake = self.0.to_case(Snake);
        let age = self.1;
        let query_spec = self.2;
        write!(f, "{relation_snake}.iter_{age}")?;
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
    signature: &Signature,
    query_action: &QueryAction,
    axiom_index: usize,
) -> io::Result<()> {
    let terms = query_action.query_terms_used_in_actions(signature);
    let term_decls = terms.into_iter().format_with("\n", |(term, sort), f| {
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

fn write_close_data_struct(
    out: &mut impl Write,
    signature: &Signature,
    query_actions: &[QueryAction],
) -> io::Result<()> {
    let query_matches = (0..query_actions.len()).format_with("\n", |i, f| {
        f(&format_args!("    query_matches_{i}: Vec<QueryMatch{i}>,"))
    });
    let functionality_matches = signature.iter_functions().format_with("\n", |func, f| {
        let Function { name, cod, .. } = func;
        let func_snake = name.to_case(Snake);
        f(&format_args!(
            "    functionality_matches_{func_snake}: Vec<({cod}, {cod})>,"
        ))
    });
    let relations_new = signature.relations().format_with("\n", |(relation, _), f| {
        let relation_snake = relation.to_case(Snake);
        f(&format_args!("    {relation_snake}_new: Vec<{relation}>,"))
    });

    writedoc! {out, "
        #[derive(Debug)]
        struct CloseData {{
        {query_matches}

        {functionality_matches}

        {relations_new}
        }}
    "}
}

fn write_close_data_impl(
    out: &mut impl Write,
    signature: &Signature,
    query_actions: &[QueryAction],
) -> io::Result<()> {
    let query_matches = (0..query_actions.len()).format_with("\n", |i, f| {
        f(&format_args!("    query_matches_{i}: Vec::new(),"))
    });
    let functionality_matches = signature.iter_functions().format_with("\n", |func, f| {
        let func_snake = func.name.to_case(Snake);
        f(&format_args!(
            "    functionality_matches_{func_snake}: Vec::new(),"
        ))
    });
    let relations_new = signature.relations().format_with("\n", |(relation, _), f| {
        let relation_snake = relation.to_case(Snake);
        f(&format_args!("    {relation_snake}_new: Vec::new(),"))
    });

    writedoc! {out, "
        impl CloseData {{
            fn new() -> CloseData {{
                CloseData{{
        {query_matches}
        {functionality_matches}
        {relations_new}
                }}
            }}
        }}
    "}
}

fn write_query_loop_headers<'a>(
    out: &mut impl Write,
    signature: &Signature,
    query_ages: impl Iterator<Item = (&'a Query, TupleAge)>,
) -> io::Result<()> {
    for (query, age) in query_ages {
        use Query::*;
        match query {
            Relation {
                relation,
                diagonals,
                projections,
                results,
            } => {
                let arity_len = signature
                    .relations()
                    .find(|(rel, _)| rel == relation)
                    .unwrap()
                    .1
                    .len();
                let query_spec = QuerySpec {
                    diagonals: diagonals.clone(),
                    projections: projections.keys().copied().collect(),
                };
                write!(out, "#[allow(unused_variables)]\n")?;
                write!(out, "for {}(", relation)?;
                for i in 0..arity_len {
                    if let Some(tm) = results.get(&i) {
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
                let iter_name = IterName(relation, age, &query_spec);
                write!(out, "{iter_name}")?;
                write!(out, "(")?;
                for tm in projections.values().copied() {
                    write!(out, "tm{}, ", tm.0)?;
                }
                write!(out, ") {{\n")?;
            }
            Sort { sort, result } => {
                write!(out, "#[allow(unused_variables)]\n")?;
                write!(
                    out,
                    "for tm{} in self.{}_{}.iter().copied() {{\n",
                    result.0,
                    sort.to_case(Snake),
                    age
                )?;
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
    signature: &Signature,
    query_action: &QueryAction,
    axiom_index: usize,
) -> io::Result<()> {
    writedoc! {out, "
        fn collect_query_matches_{axiom_index}(&self, data: &mut CloseData) {{
    "}?;

    let queries = &query_action.queries;
    if queries.is_empty() {
        writedoc! {out, "
            if self.empty_join_is_dirty {{
                data.query_matches_{axiom_index}.push(QueryMatch{axiom_index}{{}});
            }}
        "}?;
    } else {
        for new_index in 0..queries.len() {
            let query_ages = queries.iter().enumerate().map(|(i, query)| {
                let age = if i == new_index {
                    TupleAge::Dirty
                } else {
                    TupleAge::All
                };
                (query, age)
            });
            write_query_loop_headers(out, signature, query_ages)?;
            let query_terms = query_action.query_terms_used_in_actions(signature);
            let action_args = query_terms.keys().copied().format_with(", ", |tm, f| {
                let tm = tm.0;
                f(&format_args!("tm{tm}"))
            });
            write!(
                out,
                "data.query_matches_{axiom_index}.push(QueryMatch{axiom_index}{{ {action_args} }});"
            )?;
            write_query_loop_footers(out, queries.len())?;
        }
    }

    writedoc! {out, "
        }}
    "}
}

fn write_collect_functionality_matches_fn(
    out: &mut impl Write,
    function: &Function,
) -> io::Result<()> {
    let Function { name, dom, .. } = function;
    let name_snake = name.to_case(Snake);

    let dirty_query = QuerySpec::new();
    let dirty_iter = IterName(name, TupleAge::Dirty, &dirty_query);

    let all_query = QuerySpec {
        projections: (0..dom.len()).collect(),
        diagonals: BTreeSet::new(),
    };
    let all_iter = IterName(name, TupleAge::All, &all_query);

    let dirty_result = dom.len();
    let all_result = dom.len() + 1;

    let dirty_vars = (0..dom.len() + 1).format_with(", ", |i, f| f(&format_args!("tm{i}")));
    let all_vars = (0..dom.len() + 1).format_with(", ", |i, f| {
        if i < dom.len() {
            f(&format_args!("_"))
        } else {
            f(&format_args!("tm{all_result}"))
        }
    });
    let old_args = (0..dom.len()).format_with(", ", |i, f| f(&format_args!("tm{i}")));

    writedoc! {out, "
        fn collect_functionality_matches_{name_snake}(&mut self, data: &mut CloseData) {{
            for {name}({dirty_vars}) in self.{dirty_iter}() {{
                for {name}({all_vars}) in self.{all_iter}({old_args}) {{
                    data.functionality_matches_{name_snake}.push((tm{dirty_result}, tm{all_result}));
                }}
            }}
        }}
    "}
}

fn write_action(out: &mut impl Write, signature: &Signature, action: &Action) -> io::Result<()> {
    use Action::*;
    match action {
        AddTerm {
            function,
            args,
            result,
        } => {
            let function_snake = function.to_case(Snake);
            let arity = signature.arity(function).unwrap();
            let dom = &arity[0..arity.len() - 1];
            let cod = *arity.last().unwrap();
            let cod_snake = cod.to_case(Snake);
            let canonicalize_iter_args =
                args.iter().zip(dom).format_with("\n", |(arg, sort), f| {
                    let arg = arg.0;
                    let sort_snake = sort.to_case(Snake);
                    f(&format_args!(
                        "let tm{arg} = self.{sort_snake}_equalities.root(tm{arg});"
                    ))
                });
            let query_spec = QuerySpec {
                projections: (0..dom.len()).collect(),
                diagonals: BTreeSet::new(),
            };
            let iter_name = IterName(function, TupleAge::All, &query_spec);
            let iter_args = args.iter().format_with(", ", |arg, f| {
                let arg = arg.0;
                f(&format_args!("tm{arg}"))
            });
            let tuple_args = args.iter().chain(once(result)).format_with(", ", |arg, f| {
                let arg = arg.0;
                f(&format_args!("tm{arg}"))
            });
            let result = result.0;
            let dom_len = dom.len();
            writedoc! {out, "
                {canonicalize_iter_args}
                let existing_row = self.{iter_name}({iter_args}).next();
                #[allow(unused_variables)]
                let tm{result} = match existing_row {{
                    Some(t) => t.{dom_len},
                    None => {{
                        let tm{result} = self.new_{cod_snake}();
                        self.{function_snake}.insert({function}({tuple_args}));
                        tm{result}
                    }},
                }};
            "}
        }
        AddTuple { relation, args } => {
            let relation_snake = relation.to_case(Snake);
            let args = args.iter().format_with(", ", |arg, f| {
                let arg = arg.0;
                f(&format_args!("tm{arg}"))
            });
            writedoc! {out, "
                data.{relation_snake}_new.push({relation}({args}));
            "}
        }
        Equate { sort, lhs, rhs } => {
            let lhs = lhs.0;
            let rhs = rhs.0;
            let sort_snake = sort.to_case(Snake);
            let arity_contains_sort =
                |arity: &[&str]| -> bool { arity.iter().find(|s| **s == sort).is_some() };
            let clean_rels = signature
                .relations()
                .filter(|(_, arity)| arity_contains_sort(arity))
                .format_with("\n", |(relation, _), f| {
                    let relation_snake = relation.to_case(Snake);
                    f(&format_args! {"
                        data.{relation_snake}_new.extend(
                            self.{relation_snake}.drain_with_element_{sort_snake}(tm{lhs})
                        );
                    "})
                });
            writedoc! {out, "
                let tm{lhs} = self.{sort_snake}_equalities.root(tm{lhs});
                let tm{rhs} = self.{sort_snake}_equalities.root(tm{rhs});
                if tm{lhs} != tm{rhs} {{
                    self.{sort_snake}_equalities.union_roots_into(tm{lhs}, tm{rhs});
                    self.{sort_snake}_all.remove(&tm{lhs});
                    self.{sort_snake}_dirty.remove(&tm{lhs});
                    {clean_rels}
                }}
            "}
        }
    }
}

fn write_apply_actions_fn(
    out: &mut impl Write,
    signature: &Signature,
    query_action: &QueryAction,
    axiom_index: usize,
) -> io::Result<()> {
    let terms = query_action.query_terms_used_in_actions(signature);
    let unpack_args = terms.keys().format_with(", ", |tm, f| {
        let tm = tm.0;
        f(&format_args!("tm{tm}"))
    });
    writedoc! {out, "
        fn apply_actions_{axiom_index}(&mut self, data: &mut CloseData) {{
            for query_match in data.query_matches_{axiom_index}.drain(..) {{ 
                let QueryMatch{axiom_index}{{{unpack_args}}} = query_match;
    "}?;
    for action in query_action.actions.iter() {
        write_action(out, signature, action)?;
    }
    writedoc! {out, "
            }}
        }}
    "}
}

fn write_apply_functionality_fn(
    out: &mut impl Write,
    signature: &Signature,
    function: &Function,
) -> io::Result<()> {
    let function_snake = function.name.to_case(Snake);
    writedoc! {out, "
        fn apply_functionality_{function_snake}(&mut self, data: &mut CloseData) {{
            for (tm0, tm1) in data.functionality_matches_{function_snake}.drain(..) {{ 
    "}?;
    let action = Action::Equate {
        sort: function.cod.clone(),
        lhs: FlatTerm(0),
        rhs: FlatTerm(1),
    };
    write_action(out, signature, &action)?;
    writedoc! {out, "
            }}
        }}
    "}
}

fn write_forget_dirt_fn(out: &mut impl Write, signature: &Signature) -> io::Result<()> {
    let relations = signature.relations().format_with("\n", |(relation, _), f| {
        let relation_snake = relation.to_case(Snake);
        f(&format_args!("self.{relation_snake}.drop_dirt();"))
    });
    let sorts = signature.iter_sorts().format_with("\n", |sort, f| {
        let sort_snake = sort.name.to_case(Snake);
        f(&format_args!("self.{sort_snake}_dirty.clear();"))
    });
    writedoc! {out, "
        fn forget_dirt(&mut self) {{
            self.empty_join_is_dirty = false;
        {relations}
        {sorts}
        }}
    "}
}

fn write_insert_new_tuples_fn(out: &mut impl Write, signature: &Signature) -> io::Result<()> {
    let relation_tuples = signature.relations().format_with("\n", |(relation, _), f| {
        let relation_snake = relation.to_case(Snake);
        f(&format_args!(
            "
                for t in data.{relation_snake}_new.drain(..) {{
                    self.insert_{relation_snake}(t);
                }}
            "
        ))
    });
    writedoc! {out, "
        fn insert_new_tuples(&mut self, data: &mut CloseData) {{
        {relation_tuples}
        }}
    "}
}

fn write_close_fn(
    out: &mut impl Write,
    signature: &Signature,
    query_actions: &[QueryAction],
) -> io::Result<()> {
    let collect_query_matches = (0..query_actions.len()).format_with("\n", |i, f| {
        f(&format_args!(
            "            self.collect_query_matches_{i}(&mut data);"
        ))
    });
    let collect_functionality_matches = signature.iter_functions().format_with("\n", |func, f| {
        let func_snake = func.name.to_case(Snake);
        f(&format_args!(
            "            self.collect_functionality_matches_{func_snake}(&mut data);"
        ))
    });
    let is_surjective_axiom = |index: &usize| query_actions[*index].is_surjective();
    let apply_surjective_axiom_actions = (0..query_actions.len())
        .filter(is_surjective_axiom)
        .format_with("\n", |i, f| {
            f(&format_args!(
                "            self.apply_actions_{i}(&mut data);"
            ))
        });
    let apply_non_surjective_axiom_actions = (0..query_actions.len())
        .filter(|i| !is_surjective_axiom(i))
        .format_with("\n", |i, f| {
            f(&format_args!("        self.apply_actions_{i}(&mut data);"))
        });
    let apply_functionality = signature.iter_functions().format_with("\n", |function, f| {
        let function_snake = function.name.to_case(Snake);
        f(&format_args!(
            "            self.apply_functionality_{function_snake}(&mut data);"
        ))
    });
    writedoc! {out, "
        #[allow(dead_code)]
        pub fn close(&mut self) {{
            let mut data = CloseData::new();
            while self.is_dirty() {{
                loop {{
        {collect_query_matches}
        {collect_functionality_matches}
            
                    self.forget_dirt();

        {apply_surjective_axiom_actions}
        {apply_functionality}

                    self.insert_new_tuples(&mut data);
                    if !self.is_dirty() {{
                        break;
                    }}
                }}
        {apply_non_surjective_axiom_actions}
                self.insert_new_tuples(&mut data);
            }}
        }}
    "}
}

fn write_new_fn(out: &mut impl Write, signature: &Signature) -> io::Result<()> {
    write!(out, "#[allow(dead_code)]\n")?;
    write!(out, "pub fn new() -> Self {{\n")?;
    write!(out, "Self {{\n")?;
    for sort in signature.iter_sorts() {
        let sort_snake = sort.name.to_case(Snake);
        write!(out, "{sort_snake}_equalities: Unification::new(),\n")?;
        write!(out, "{}_dirty: BTreeSet::new(),\n", sort_snake)?;
        write!(out, "{}_all: BTreeSet::new(),\n", sort_snake)?;
    }
    for (relation, _) in signature.relations() {
        let relation_snake = relation.to_case(Snake);
        write!(out, "{relation_snake}: {relation}Table::new(),")?;
    }
    write!(out, "empty_join_is_dirty: true,\n")?;
    write!(out, "}}\n")?;
    write!(out, "}}\n")?;
    Ok(())
}

fn write_theory_struct(out: &mut impl Write, name: &str, signature: &Signature) -> io::Result<()> {
    write!(out, "#[derive(Debug)]\n")?;
    write!(out, "pub struct {} {{\n", name)?;
    for sort in signature.iter_sorts() {
        write_sort_fields(out, &sort.name)?;
        write!(out, "\n")?;
    }

    for (relation, _) in signature.relations() {
        let relation_snake = relation.to_case(Snake);
        write!(out, "  {relation_snake}: {relation}Table,")?;
    }

    write!(out, "empty_join_is_dirty: bool,\n")?;
    write!(out, "}}\n")?;
    Ok(())
}

fn write_theory_impl(
    out: &mut impl Write,
    name: &str,
    signature: &Signature,
    query_actions: &[QueryAction],
) -> io::Result<()> {
    write!(out, "impl {} {{\n", name)?;
    for sort in signature.iter_sorts() {
        write_new_element(out, &sort.name)?;
        write_iter_sort_fn(out, &sort.name)?;
        write_sort_root_fn(out, &sort.name)?;
        write!(out, "\n")?;
    }
    for (rel, arity) in signature.relations() {
        write_pub_iter_fn(out, rel)?;
        write_pub_insert_relation(out, rel, &arity)?;
        write!(out, "\n")?;
    }

    write_new_fn(out, signature)?;
    write!(out, "\n")?;

    write_is_dirty_fn(out, signature)?;
    write!(out, "\n")?;

    for (i, query_action) in query_actions.iter().enumerate() {
        write_collect_query_matches_fn(out, signature, query_action, i)?;
        write_apply_actions_fn(out, signature, query_action, i)?;
    }
    for function in signature.iter_functions() {
        write_collect_functionality_matches_fn(out, function)?;
        write_apply_functionality_fn(out, signature, function)?;
    }

    write_forget_dirt_fn(out, signature)?;
    write_insert_new_tuples_fn(out, signature)?;
    write_close_fn(out, signature, query_actions)?;

    write!(out, "}}\n")?;
    Ok(())
}

pub fn write_module(
    out: &mut impl Write,
    name: &str,
    signature: &Signature,
    query_actions: &[QueryAction],
    index_selection: &IndexSelection,
) -> io::Result<()> {
    write_imports(out)?;
    write!(out, "\n")?;

    for sort in signature.iter_sorts() {
        write_sort_struct(out, &sort.name)?;
        write_sort_impl(out, &sort.name)?;
    }
    write!(out, "\n")?;

    for (rel, arity) in signature.relations() {
        write_relation_struct(out, rel, &arity)?;
        let index = index_selection.get(rel).unwrap();
        write_table_struct(out, rel, &arity, index)?;
        write_table_impl(out, rel, &arity, index)?;
    }
    write!(out, "\n")?;

    for (i, qa) in query_actions.iter().enumerate() {
        write_query_match_struct(out, signature, qa, i)?;
        write!(out, "\n")?;
    }

    write_close_data_struct(out, signature, query_actions)?;
    write_close_data_impl(out, signature, query_actions)?;
    write!(out, "\n")?;

    write_theory_struct(out, name, signature)?;
    write_theory_impl(out, name, signature, query_actions)?;

    Ok(())
}
