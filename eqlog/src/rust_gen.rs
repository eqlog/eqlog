use crate::direct_ast::*;
use crate::flat_ast::FlatTerm;
use crate::index_selection::*;
use crate::query_action::*;
use crate::signature::Signature;
use convert_case::{Case, Casing};
use indoc::writedoc;
use itertools::Itertools;
use std::collections::BTreeSet;
use std::fmt::{self, Display, Formatter};
use std::io::{self, Write};
use std::iter::once;

use Case::Snake;

fn write_imports(out: &mut impl Write) -> io::Result<()> {
    writedoc! { out, "
        use std::collections::BTreeSet;
        use std::collections::HashSet;
        use eqlog_util::Unification;
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
        {sort_snake}_all: HashSet<{sort}>,
        {sort_snake}_dirty: HashSet<{sort}>,
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

fn write_relation_field(out: &mut impl Write, relation: &str, age: TupleAge) -> io::Result<()> {
    let relation_snake = relation.to_case(Snake);
    writedoc! {out, "
        {relation_snake}_{age} : BTreeSet<{relation}>,
    "}
}

fn write_is_dirty_fn(out: &mut impl Write, signature: &Signature) -> io::Result<()> {
    let rels_dirty = signature
        .relations()
        .format_with(" || ", |(relation, _), f| {
            let relation_snake = relation.to_case(Snake);
            f(&format_args!("!self.{relation_snake}_dirty.is_empty()"))
        });

    let sorts_dirty = signature.sorts().keys().format_with(" || ", |sort, f| {
        let sort_snake = sort.to_case(Snake);
        f(&format_args!("!self.{sort_snake}_dirty.is_empty()"))
    });

    writedoc! {out, "
        #[allow(dead_code)]
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
        write!(f, "iter_{relation_snake}_{age}")?;
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

fn write_iter_fn(
    out: &mut impl Write,
    relation: &str,
    arity: &[&str],
    query: &QuerySpec,
    age: TupleAge,
) -> io::Result<()> {
    let relation_snake = relation.to_case(Snake);
    let iter_name = IterName(relation, age, query);

    // (arg3: Mor, arg5: Obj, ...)
    let args = query.projections.iter().copied().format_with(", ", |i, f| {
        let sort = arity[i];
        f(&format_args!("arg{i}: {sort}"))
    });

    // && _t.3 == arg3 && _t.5 == arg5 ...
    let projs_match = query
        .projections
        .iter()
        .copied()
        .format_with("", |i, f| f(&format_args!(" && _t.{i} == arg{i}")));

    // let diag0_matches = _t.1 == _t.2 && _t.2 == _t.4 && ...;
    // let diag1_matches = _t.3 == _t.8;
    // ...
    let diags_match_decls = query
        .diagonals
        .iter()
        .enumerate()
        .format_with("\n", |(d, diag), f| {
            let clauses = diag
                .iter()
                .zip(diag.iter().skip(1))
                .format_with(" && ", |(prev, next), f| {
                    f(&format_args!("_t.{prev} == _t.{next}"))
                });
            f(&format_args!("let diag{d}_matches = {clauses};"))
        });

    // && diag0_matches && diag_1_matches ...
    let diags_match =
        (0..query.diagonals.len()).format_with("", |d, f| f(&format_args!(" && diag{d}_matches")));

    writedoc! {out, "
        #[allow(dead_code)]
        fn {iter_name}(&self, {args}) -> impl '_ + Iterator<Item={relation}> {{
            self.{relation_snake}_{age}.iter().filter(move |_t| {{
                let proj_matches = true {projs_match};
                {diags_match_decls}
                proj_matches {diags_match}
            }}).copied()
        }}
    "}
}

fn write_pub_iter_fn(out: &mut impl Write, relation: &str) -> io::Result<()> {
    let rel_snake = relation.to_case(Snake);
    writedoc! {out, "
        #[allow(dead_code)]
        pub fn iter_{rel_snake}(&self) -> impl '_ + Iterator<Item={relation}> {{
            self.iter_{rel_snake}_all()
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
            if self.{relation_snake}_all.insert(t) {{
                self.{relation_snake}_dirty.insert(t);
            }}
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
    let functionality_matches = signature.functions().values().format_with("\n", |func, f| {
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
    let functionality_matches = signature.functions().values().format_with("\n", |func, f| {
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
            write!(out, "// Query {new_index} is for dirty data.\n")?;
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
            let Function { dom, cod, .. } = signature.functions().get(function).unwrap();
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
                        self.insert_{function_snake}({function}({tuple_args}));
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
                .format_with("\n", |(relation, arity), f| {
                    let relation_snake = relation.to_case(Snake);
                    let clauses = arity
                        .iter()
                        .enumerate()
                        .filter(|(_, s)| **s == sort)
                        .format_with(" || ", |(i, _), f| f(&format_args!("t.{i} == tm{lhs}")));
                    f(&format_args!(
                        "
                        let {relation_snake}_contains_lhs = |t: &{relation}| {clauses};
                        data.{relation_snake}_new.extend(
                            self.iter_{relation_snake}()
                            .filter({relation_snake}_contains_lhs)
                        );
                        self.{relation_snake}_all.retain(|t| !{relation_snake}_contains_lhs(t));
                    "
                    ))
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
        f(&format_args!("self.{relation_snake}_dirty.clear();"))
    });
    let sorts = signature.sorts().keys().format_with("\n", |sort, f| {
        let sort_snake = sort.to_case(Snake);
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
    let collect_functionality_matches =
        signature.functions().keys().format_with("\n", |func, f| {
            let func_snake = func.to_case(Snake);
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
    let apply_functionality = signature
        .functions()
        .keys()
        .format_with("\n", |function, f| {
            let function_snake = function.to_case(Snake);
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
    for sort in signature.sorts().keys() {
        write!(
            out,
            "{}_equalities: Unification::new(),\n",
            sort.to_case(Snake)
        )?;
        write!(out, "{}_dirty: HashSet::new(),\n", sort.to_case(Snake))?;
        write!(out, "{}_all: HashSet::new(),\n", sort.to_case(Snake))?;
    }
    for (relation, _) in signature.relations() {
        write!(out, "{}_all: BTreeSet::new(),\n", relation.to_case(Snake))?;
        write!(out, "{}_dirty: BTreeSet::new(),\n", relation.to_case(Snake))?;
    }
    write!(out, "empty_join_is_dirty: true,\n")?;
    write!(out, "}}\n")?;
    write!(out, "}}\n")?;
    Ok(())
}

fn write_theory_struct(out: &mut impl Write, name: &str, signature: &Signature) -> io::Result<()> {
    write!(out, "#[derive(Debug)]\n")?;
    write!(out, "pub struct {} {{\n", name)?;
    for sort in signature.sorts().keys() {
        write_sort_fields(out, sort.as_str())?;
        write!(out, "\n")?;
    }

    for (rel, _) in signature.relations() {
        write_relation_field(out, rel, TupleAge::All)?;
        write_relation_field(out, rel, TupleAge::Dirty)?;
        write!(out, "\n")?;
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
    index_selection: &IndexSelection,
) -> io::Result<()> {
    write!(out, "impl {} {{\n", name)?;
    for sort in signature.sorts().keys() {
        write_new_element(out, sort)?;
        write_iter_sort_fn(out, sort)?;
        write_sort_root_fn(out, sort)?;
        write!(out, "\n")?;
    }
    for (rel, arity) in signature.relations() {
        let query_index_map = index_selection.get(rel).unwrap();
        for query in query_index_map.keys() {
            write_iter_fn(out, rel, &arity, query, TupleAge::All)?;
            write_iter_fn(out, rel, &arity, query, TupleAge::Dirty)?;
        }
        let unrestrained_query = QuerySpec::new();
        if let None = query_index_map.get(&unrestrained_query) {
            write_iter_fn(out, rel, &arity, &unrestrained_query, TupleAge::All)?;
            write_iter_fn(out, rel, &arity, &unrestrained_query, TupleAge::Dirty)?;
        };
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
    for function in signature.functions().values() {
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

    for sort in signature.sorts().keys() {
        write_sort_struct(out, sort)?;
        write_sort_impl(out, sort)?;
    }
    write!(out, "\n")?;

    for (rel, arity) in signature.relations() {
        write_relation_struct(out, rel, &arity)?;
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
    write_theory_impl(out, name, signature, query_actions, index_selection)?;

    Ok(())
}
