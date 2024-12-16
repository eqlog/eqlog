use crate::eqlog_util::*;
use crate::flat_eqlog::*;
use crate::fmt_util::*;
use by_address::ByAddress;
use convert_case::{Case, Casing};
use eqlog_eqlog::*;
use indoc::{formatdoc, writedoc};
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Display, Formatter, Result};
use std::io::{self, Write};
use std::iter::once;
use std::iter::repeat;

use Case::{Snake, UpperCamel};

fn from_singleton<T>(supposed_singleton: &[T]) -> &T {
    let mut iter = supposed_singleton.into_iter();
    let value = iter.next().expect("Supposed singleton is empty");
    assert!(
        iter.next().is_none(),
        "Supposed singleton contains more than one element"
    );
    value
}

fn display_symbol_scope_name<'a>(
    sym_scope: SymbolScope,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| {
        let sym_scope_name = eqlog.symbol_scope_name(sym_scope).unwrap();
        let sym_scope_camel = identifiers
            .get(&sym_scope_name)
            .unwrap()
            .as_str()
            .to_case(UpperCamel);
        let is_top_level = eqlog.iter_module_node().any(|module| {
            eqlog.are_equal_symbol_scope(eqlog.module_symbol_scope(module).unwrap(), sym_scope)
        });
        if is_top_level {
            write!(f, "{sym_scope_camel}")?;
        } else {
            write!(f, "{sym_scope_camel}Model")?;
        }
        Ok(())
    })
}

fn display_symbol_scope_delta_name<'a>(
    sym_scope: SymbolScope,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| {
        let sym_scope_name = display_symbol_scope_name(sym_scope, eqlog, identifiers);
        write!(f, "{sym_scope_name}Delta")?;
        Ok(())
    })
}

fn display_func_snake<'a>(
    func: Func,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    let ident = eqlog
        .iter_semantic_func()
        .find_map(|(_, ident, func0)| eqlog.are_equal_func(func, func0).then_some(ident))
        .expect("should be surjective");
    format!("{}", identifiers.get(&ident).unwrap()).to_case(Snake)
}

fn write_imports(out: &mut impl Write) -> io::Result<()> {
    writedoc! { out, "
        #[allow(unused)]
        use std::collections::{{BTreeSet, BTreeMap}};
        #[allow(unused)]
        use std::fmt;
        #[allow(unused)]
        use eqlog_runtime::Unification;
        #[allow(unused)]
        use std::ops::Bound;
        #[allow(unused)]
        use std::cell::RefCell;
    "}
}

fn display_type_struct<'a>(
    typ: Type,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let type_name = display_type(typ, eqlog, identifiers);
        writedoc! {f, "
            #[allow(dead_code)]
            #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
            pub struct {type_name}(pub u32);
        "}
    })
}

fn display_var_type<'a>(
    typ: Type,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    let type_ident = eqlog.type_name(typ).unwrap();
    let type_name_camel = identifiers.get(&type_ident).unwrap().to_case(UpperCamel);
    FmtFn(move |f: &mut Formatter| -> Result { write!(f, "{type_name_camel}Var") })
}

fn display_type_var_struct_and_impl<'a>(
    typ: Type,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    let var_type = display_var_type(typ, eqlog, identifiers);
    FmtFn(move |f: &mut Formatter| -> Result {
        let type_name = display_type(typ, eqlog, identifiers);
        writedoc! {f, "
            #[allow(dead_code)]
            #[derive(Copy, Clone)]
            pub struct {var_type}<'a> {{
            var: {type_name},
            phantom: std::marker::PhantomData<&'a ()>,
        "}?;

        let member_scope = eqlog.model_member_symbol_scope(typ);
        if let Some(member_scope) = member_scope {
            let model_struct_name = display_symbol_scope_name(member_scope, eqlog, identifiers);
            writedoc! {f, "
                model: Option<&'a RefCell<{model_struct_name}>>,
            "}?;
        }

        writedoc! {f, "
            }}
        "}?;

        writedoc! {f, "
            #[allow(dead_code)]
            impl<'a> {var_type}<'a> {{
            fn new(var: {type_name}) -> Self {{
            Self {{
            var,
            phantom: std::marker::PhantomData,
        "}?;
        if let Some(_) = member_scope {
            writedoc! {f, "
                model: None,
            "}?;
        }
        writedoc! {f, "
            }}
            }}
        "}?;

        if let Some(member_scope) = member_scope {
            let model_struct_name = display_symbol_scope_name(member_scope, eqlog, identifiers);
            writedoc! {f, "
                fn get_model(&mut self, models: &'a BTreeMap<{type_name}, RefCell<{model_struct_name}>>) -> std::cell::Ref<'a, {model_struct_name}> {{
                let ref_cell = self.model.get_or_insert_with(|| models.get(&self.var).unwrap());
                ref_cell.borrow()
                }}
            "}?;
        }

        writedoc! {f, "
            }}
        "}?;

        Ok(())
    })
}

fn display_type_impl<'a>(
    typ: Type,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let type_name = display_type(typ, eqlog, identifiers);
        writedoc! {f, "
            impl Into<u32> for {type_name} {{ fn into(self) -> u32 {{ self.0 }} }}
            impl From<u32> for {type_name} {{ fn from(x: u32) -> Self {{ {type_name}(x) }} }}
            impl fmt::Display for {type_name} {{
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {{
                    write!(f, \"{{:?}}\", self)
                }}
            }}
        "}
    })
}

fn display_ctor<'a>(
    ctor: CtorDeclNode,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let ctor_ident = eqlog
            .iter_ctor_decl()
            .find_map(|(ctor0, ctor_ident, _)| {
                if eqlog.are_equal_ctor_decl_node(ctor0, ctor) {
                    Some(ctor_ident)
                } else {
                    None
                }
            })
            .unwrap();

        let ctor_name: String = identifiers.get(&ctor_ident).unwrap().to_case(UpperCamel);
        let ss: SymbolScope = eqlog.ctor_symbol_scope(ctor).unwrap();

        let ctor_func = eqlog.semantic_func(ss, ctor_ident).unwrap();
        let domain: Vec<Type> =
            type_list_vec(eqlog.domain(ctor_func).expect("should be total"), eqlog);

        let domain = domain
            .into_iter()
            .map(|typ| display_type(typ, eqlog, identifiers))
            .format(", ");

        write!(f, "{}({})", ctor_name, domain)
    })
}

fn display_enum<'a>(
    enum_decl: EnumDeclNode,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let ctors = eqlog
            .iter_ctor_enum()
            .filter_map(|(ctor, enum_decl0)| {
                if eqlog.are_equal_enum_decl_node(enum_decl, enum_decl0) {
                    Some(ctor)
                } else {
                    None
                }
            })
            .map(|ctor| format!("{},\n", display_ctor(ctor, eqlog, identifiers)))
            .format("");

        let enum_ident = eqlog
            .iter_enum_decl()
            .find_map(|(enum_decl0, enum_ident, _)| {
                if eqlog.are_equal_enum_decl_node(enum_decl, enum_decl0) {
                    Some(enum_ident)
                } else {
                    None
                }
            })
            .unwrap();
        let enum_name = identifiers.get(&enum_ident).unwrap().to_case(UpperCamel);

        writedoc! {f, "
            #[allow(unused)]
            #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
            pub enum {enum_name}Case {{
            {ctors}
            }}
        "}
    })
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
        #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
        struct {relation_camel}({args});
    "}
}

fn write_func_args_struct(out: &mut impl Write, func: &str, dom: &[&str]) -> io::Result<()> {
    let func_camel = func.to_case(UpperCamel);
    let args = dom
        .iter()
        .copied()
        .format_with(", ", |typ, f| f(&format_args!("pub {typ}")));
    // The #[allow(unused)] is there for functions that cannot be made defined via the Rust API. At
    // the moment, those are non-constructor functions valued in an enum type.
    writedoc! {out, "
        #[allow(unused)]
        #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
        struct {func_camel}Args({args});
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

fn write_table_struct(
    out: &mut impl Write,
    relation: &str,
    arity: &[&str],
    indices: &BTreeSet<&IndexSpec>,
) -> io::Result<()> {
    let tuple_type_args = (0..arity.len()).format_with("", |_, f| f(&format_args!("u32, ")));
    let tuple_type = format!("({tuple_type_args})");

    let index_fields = indices.iter().copied().format_with("\n", |index, f| {
        let index_name = IndexName(index);
        f(&format_args!(
            "    index_{index_name}: BTreeSet<{tuple_type}>,"
        ))
    });

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
        {element_index_fields}
        }}
    "}
}

fn write_table_new_fn(
    out: &mut impl Write,
    arity: &[&str],
    indices: &BTreeSet<&IndexSpec>,
) -> io::Result<()> {
    let index_inits = indices.iter().copied().format_with("\n", |index, f| {
        let index_name = IndexName(index);
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

fn write_table_insert_fn(
    out: &mut impl Write,
    relation: &str,
    arity: &[&str],
    indices: &BTreeSet<&IndexSpec>,
    index_selection: &BTreeMap<QuerySpec, Vec<IndexSpec>>,
) -> io::Result<()> {
    let (master_new_index, master_old_index) =
        match index_selection.get(&QuerySpec::all()).unwrap().as_slice() {
            [a, b] => {
                let (new_index, old_index) = if a.age == IndexAge::New {
                    (a, b)
                } else {
                    (b, a)
                };
                assert!(
                    new_index.age == IndexAge::New,
                    "Master indices should be given by a new index and an old index"
                );
                assert!(
                    old_index.age == IndexAge::Old,
                    "Master indices should be given by a new index and an old index"
                );
                (new_index, old_index)
            }
            indices => panic!(
                "Expected exactly QuerySpec::all to be served by two indices, found {:?} indices",
                indices.len()
            ),
        };
    let master_new = IndexName(master_new_index);
    let master_old = IndexName(master_old_index);

    let master_new_order = OrderName(&master_new_index.order);
    let master_old_order = OrderName(&master_old_index.order);

    let slave_inserts = indices
        .into_iter()
        .filter(|index| index.age != IndexAge::Old && **index != master_new_index)
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
            // NOTE: Can't this be done with `entry(...).or_insert_with(...)` as well though?
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
        if self.index_{master_old}.contains(&Self::permute{master_old_order}(t)) {{
        return false;
        }}
        if !self.index_{master_new}.insert(Self::permute{master_new_order}(t)) {{
        return false;
        }}

        {slave_inserts}
        {element_inserts}
        true
        }}
    "}
}

struct QueryName<'a>(&'a QuerySpec);

impl<'a> Display for QueryName<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let query = self.0;
        let age_str = match query.age {
            QueryAge::New => "new",
            QueryAge::Old => "old",
            QueryAge::All => "all",
        };
        write!(f, "{age_str}")?;
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
    indices: &[IndexSpec],
) -> io::Result<()> {
    // (arg3: Mor, arg5: Obj, ...)
    let fn_args = query.projections.iter().copied().format_with(", ", |i, f| {
        let sort = arity[i];
        f(&format_args!("arg{i}: {sort}"))
    });

    let fixed_arg_len = query.projections.len();
    let open_arg_len = arity.len() - query.projections.len();
    let query_name = QueryName(query);

    let unalias_args = query
        .projections
        .iter()
        .copied()
        .format_with("\n", |i, f| f(&format_args!("    let arg{i} = arg{i}.0;")));

    let relation_camel = relation.to_case(UpperCamel);

    let mut index_iters = indices.iter().map(|index| {
        FmtFn(move |f| {
            let index_name = IndexName(index);
            let order_name = OrderName(&index.order);

            let fixed_args = || {
                index.order[..fixed_arg_len]
                    .iter()
                    .format_with("", |i, f| f(&format_args!("arg{i}, ")))
            };
            let fixed_args_min = fixed_args();
            let fixed_args_max = fixed_args();

            let open_args_min =
                (0..open_arg_len).format_with("", |_, f| f(&format_args!("u32::MIN, ")));
            let open_args_max =
                (0..open_arg_len).format_with("", |_, f| f(&format_args!("u32::MAX, ")));

            writedoc! {f, "
                self.index_{index_name}
                    .range((
                        Bound::Included(&({fixed_args_min} {open_args_min})),
                        Bound::Included(&({fixed_args_max} {open_args_max}))
                    ))
                    .copied()
                    .map(Self::permute_inverse{order_name})
            "}
        })
    });

    writedoc! {out, "
        #[allow(dead_code)]
        fn iter_{query_name}(&self, {fn_args}) -> impl '_ + Iterator<Item = {relation_camel}> {{
        {unalias_args}
    "}?;

    let first_index_iter = index_iters
        .next()
        .expect("there should be at least one index per query");
    writedoc! {out, "{first_index_iter}"}?;
    for index_iter in index_iters {
        writedoc! {out, ".chain({index_iter})"}?;
    }

    writedoc! {out, "
        }}
    "}?;

    Ok(())
}

fn write_table_contains_fn(
    out: &mut impl Write,
    relation: &str,
    index_selection: &BTreeMap<QuerySpec, Vec<IndexSpec>>,
) -> io::Result<()> {
    let indices = index_selection.get(&QuerySpec::all()).unwrap();
    let relation_camel = relation.to_case(UpperCamel);
    let checks = indices
        .iter()
        .map(|index| {
            FmtFn(|f| {
                let index_name = IndexName(index);
                let order_name = OrderName(&index.order);
                writedoc! {f, "
                self.index_{index_name}.contains(&Self::permute{order_name}(t))
            "}
            })
        })
        .format(" || ");
    writedoc! {out, "
        #[allow(dead_code)]
        fn contains(&self, t: {relation_camel}) -> bool {{
            {checks}
        }}
    "}
}

fn write_table_is_dirty_fn(
    out: &mut impl Write,
    index_selection: &BTreeMap<QuerySpec, Vec<IndexSpec>>,
) -> io::Result<()> {
    // A "new" query is always mapped to a single index at the moment.
    let master_index_new = from_singleton(
        index_selection
            .get(&QuerySpec::all_dirty())
            .unwrap()
            .as_slice(),
    );
    let master_index_new = IndexName(master_index_new);

    writedoc! {out, "
        fn is_dirty(&self) -> bool {{
            !self.index_{master_index_new}.is_empty()
        }}
    "}
}

fn write_table_drop_dirt_fn(
    out: &mut impl Write,
    indices: &BTreeSet<&IndexSpec>,
    index_selection: &BTreeMap<QuerySpec, Vec<IndexSpec>>,
) -> io::Result<()> {
    let master_index_new = from_singleton(index_selection.get(&QuerySpec::all_dirty()).unwrap());
    let master_index_new_order = OrderName(&master_index_new.order);
    let master_index_new = IndexName(master_index_new);

    let old_extends = indices
        .iter()
        .copied()
        .filter(|index| index.age == IndexAge::Old)
        .map(|index| {
            FmtFn(|f| {
                let index_name = IndexName(index);
                let index_order = OrderName(&index.order);
                writedoc!{f, "
                    self.index_{index_name}.extend(
                        self.index_{master_index_new}
                        .iter().copied()
                        .map(|t| Self::permute{index_order}(Self::permute_inverse{master_index_new_order}(t)))
                    );
                "}
            })
        })
        .format("\n");

    let new_clears = indices
        .iter()
        .copied()
        .filter(|index| index.age == IndexAge::New)
        .map(|index| {
            FmtFn(move |f| {
                let index_name = IndexName(index);
                writedoc! {f, "
                    self.index_{index_name}.clear();
                "}
            })
        })
        .format("\n");
    writedoc! {out, "
        fn drop_dirt(&mut self) {{
        {old_extends}
        {new_clears}
        }}
    "}
}

fn write_table_drain_with_element(
    out: &mut impl Write,
    relation: &str,
    indices: &BTreeSet<&IndexSpec>,
    index_selection: &BTreeMap<QuerySpec, Vec<IndexSpec>>,
    sort: &str,
) -> io::Result<()> {
    let sort_snake = sort.to_case(Snake);

    let (master_new_index, master_old_index) =
        match index_selection.get(&QuerySpec::all()).unwrap().as_slice() {
            [a, b] => {
                let (new_index, old_index) = if a.age == IndexAge::New {
                    (a, b)
                } else {
                    (b, a)
                };
                assert!(
                    new_index.age == IndexAge::New,
                    "Master indices should be given by a new index and an old index"
                );
                assert!(
                    old_index.age == IndexAge::Old,
                    "Master indices should be given by a new index and an old index"
                );
                (new_index, old_index)
            }
            indices => panic!(
                "Expected exactly QuerySpec::all to be served by two indices, found {:?} indices",
                indices.len()
            ),
        };
    let master_new = IndexName(master_new_index);
    let master_old = IndexName(master_old_index);

    let master_new_order = OrderName(&master_new_index.order);
    let master_old_order = OrderName(&master_old_index.order);

    let slave_new_removes = indices
        .into_iter()
        .filter(|index| index.age == IndexAge::New && *index != &master_new_index)
        .format_with("\n", |index, f| {
            let index_name = IndexName(index);
            let order_name = OrderName(&index.order);
            f(&format_args!(
                "self.index_{index_name}.remove(&Self::permute{order_name}(t));"
            ))
        });

    let slave_old_removes = indices
        .into_iter()
        .filter(|index| index.age == IndexAge::Old && *index != &master_old_index)
        .format_with("\n", |index, f| {
            let index_name = IndexName(index);
            let order_name = OrderName(&index.order);
            f(&format_args!(
                "self.index_{index_name}.remove(&Self::permute{order_name}(t));"
            ))
        });

    let relation_camel = relation.to_case(UpperCamel);
    writedoc! {out, "
        #[allow(dead_code)]
        fn drain_with_element_{sort_snake}(&mut self, tm: {sort}) -> Vec<{relation_camel}> {{
            let mut ts = match self.element_index_{sort_snake}.remove(&tm) {{
                None => Vec::new(),
                Some(tuples) => tuples,
            }};

            let mut i = 0;
            while i < ts.len() {{
                let t = ts[i];
                if self.index_{master_new}.remove(&Self::permute{master_new_order}(t)) {{
                    {slave_new_removes}
                    i += 1;
                }} else if self.index_{master_old}.remove(&Self::permute{master_old_order}(t)) {{
                    {slave_old_removes}
                    i += 1;
                }} else {{
                    ts.swap_remove(i);
                }}
            }}

            ts
        }}
    "}
}

fn write_table_weight(
    out: &mut impl Write,
    arity: &[&str],
    indices: &BTreeSet<&IndexSpec>,
) -> io::Result<()> {
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
    indices: &BTreeSet<&IndexSpec>,
    index_selection: &BTreeMap<QuerySpec, Vec<IndexSpec>>,
) -> io::Result<()> {
    let relation_camel = relation.to_case(UpperCamel);
    writedoc! {out, "
        impl {relation_camel}Table {{
    "}?;
    write_table_weight(out, arity, &indices)?;
    write_table_new_fn(out, arity, &indices)?;
    write_table_insert_fn(out, relation, arity, &indices, index_selection)?;
    write_table_contains_fn(out, relation, index_selection)?;
    write_table_drop_dirt_fn(out, &indices, index_selection)?;
    write_table_is_dirty_fn(out, index_selection)?;

    let index_orders: BTreeSet<&[usize]> =
        indices.iter().map(|index| index.order.as_slice()).collect();
    for order in index_orders {
        write_table_permute_fn(out, relation, arity, order)?;
        write_table_permute_inverse_fn(out, relation, arity, order)?;
    }
    for (query, indices) in index_selection.iter() {
        write_table_iter_fn(out, relation, arity, query, indices.as_slice())?;
    }
    for sort in arity.iter().copied().collect::<BTreeSet<&str>>() {
        write_table_drain_with_element(out, relation, &indices, index_selection, sort)?;
    }
    writedoc! {out, "
        }}
    "}
}

fn display_is_dirty_fn<'a>(
    sym_scope: SymbolScope,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let rels_dirty = iter_symbol_scope_relations(sym_scope, eqlog)
            .map(|rel| {
                let relation_snake = identifiers
                    .get(&eqlog.rel_name(rel).unwrap())
                    .unwrap()
                    .as_str()
                    .to_case(Snake);
                FmtFn(move |f: &mut Formatter| -> Result {
                    write!(f, " || self.{relation_snake}.is_dirty()")
                })
            })
            .format("");

        let sorts_dirty = iter_symbol_scope_types(sym_scope, eqlog)
            .map(|typ| {
                let sort_snake = identifiers
                    .get(&eqlog.type_name(typ).unwrap())
                    .unwrap()
                    .as_str()
                    .to_case(Snake);
                FmtFn(move |f: &mut Formatter| -> Result {
                    write!(f, " || !self.{sort_snake}_new.is_empty()")
                })
            })
            .format("");

        let uprooted_dirty = iter_symbol_scope_types(sym_scope, eqlog)
            .map(|typ| {
                let type_snake = identifiers
                    .get(&eqlog.type_name(typ).unwrap())
                    .unwrap()
                    .as_str()
                    .to_case(Snake);
                FmtFn(move |f: &mut Formatter| -> Result {
                    write!(f, " || !self.{type_snake}_uprooted.is_empty()")
                })
            })
            .format("");

        let nested_models_dirty = iter_symbol_scope_types(sym_scope, eqlog)
            .filter_map(|typ| {
                (eqlog.is_model_type(typ)).then_some(())?;
                let type_snake = identifiers
                    .get(&eqlog.type_name(typ).unwrap())
                    .unwrap()
                    .as_str()
                    .to_case(Snake);
                Some(FmtFn(move |f: &mut Formatter| -> Result {
                    write!(
                        f,
                        " || self.{type_snake}_models.values().any(|model| model.borrow().is_dirty())"
                    )
                }))
            })
            .format("");

        writedoc! {f, "
            pub fn is_dirty(&self) -> bool {{
                self.empty_join_is_dirty
                    {rels_dirty}
                    {sorts_dirty}
                    {uprooted_dirty}
                    {nested_models_dirty}
            }}
        "}
    })
}

fn display_merge_fn<'a>(
    sym_scope: SymbolScope,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let sym_scope_types: BTreeSet<Type> = iter_symbol_scope_types(sym_scope, eqlog).collect();
        let sym_scope_types = &sym_scope_types;
        let el_maps = sym_scope_types
            .iter()
            .copied()
            .map(|typ| {
                let type_snake = identifiers
                    .get(&eqlog.type_name(typ).unwrap())
                    .unwrap()
                    .as_str()
                    .to_case(Snake);
                let type_camel = type_snake.to_case(UpperCamel);
                FmtFn(move |f: &mut Formatter| -> Result {
                    // el_map is unused for types that don't occur in relations.
                    // TODO: We don't need to build this map for those types.
                    writedoc! {f, "
                        #[allow(unused)]
                        let {type_snake}_el_map: BTreeMap<{type_camel}, {type_camel}> =
                        other
                        .iter_{type_snake}()
                        .map(|other_el| {{
                        let self_el = self.new_{type_snake}_internal();
                        (other_el, self_el)
                        }})
                        .collect();
                    "}
                })
            })
            .format("\n");

        let rel_copy = iter_symbol_scope_relations(sym_scope, eqlog)
            .map(|rel| {
                let rel_snake = identifiers
                    .get(&eqlog.rel_name(rel).unwrap())
                    .unwrap()
                    .as_str()
                    .to_case(Snake);
                let rel_camel = rel_snake.to_case(UpperCamel);
                let arity = type_list_vec(eqlog.arity(rel).unwrap(), eqlog);
                let arity_len = arity.len();

                let apply_map_el = arity
                    .into_iter()
                    .enumerate()
                    .map(|(i, arg_type)| {
                        FmtFn(move |f| {
                            let arg_type_snake = display_type(arg_type, eqlog, identifiers)
                                .to_string()
                                .to_case(Snake);

                            writedoc! {f, "
                                let t{i} = other.{arg_type_snake}_equalities.root(t{i});
                            "}?;
                            // We only need to apply the mapping if the type is a member type (as
                            // opposed to an ambient type).
                            if sym_scope_types.contains(&arg_type) {
                                writedoc! {f, "
                                    let t{i} = *{arg_type_snake}_el_map.get(&t{i}).unwrap();
                                "}?;
                            }
                            Ok(())
                        })
                    })
                    .format("");

                let args0 = (0..arity_len)
                    .map(|i| FmtFn(move |f| write!(f, "t{i}")))
                    .format(", ");
                let args1 = args0.clone();

                FmtFn(move |f: &mut Formatter| -> Result {
                    writedoc! {f, "
                        for {rel_camel}({args0}) in other.{rel_snake}.iter_all() {{
                        {apply_map_el}
                        self.insert_{rel_snake}({args1});
                        }}
                    "}
                })
            })
            .format("\n");

        let model_copy = iter_symbol_scope_types(sym_scope, eqlog)
            .filter(|typ| eqlog.is_model_type(*typ))
            .map(|typ| {
                let type_snake = identifiers
                    .get(&eqlog.type_name(typ).unwrap())
                    .unwrap()
                    .as_str()
                    .to_case(Snake);
                FmtFn(move |f: &mut Formatter| -> Result {
                    writedoc! {f, "
                        for (el, model) in other.{type_snake}_models.into_iter() {{
                        let el =
                        *{type_snake}_el_map.get(
                        &other.{type_snake}_equalities.root(el)
                        ).unwrap();
                        self.{type_snake}_models.insert(el, model);
                        }}
                    "}
                })
            })
            .format("\n");

        // The `mut` declaration for `other` is unused in case all of the {apply_map_el} blocks are
        // empty, i.e. if the symbol scope contains at most nullary predicates and no functions.
        writedoc! {f, "
            #[allow(unused_mut)]
            pub fn merge(&mut self, mut other: Self) {{
            self.empty_join_is_dirty |= other.empty_join_is_dirty;

            {el_maps}

            {rel_copy}

            {model_copy}
            }}
        "}
    })
}

struct IterName<'a>(&'a str, &'a QuerySpec);

impl<'a> Display for IterName<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let IterName(relation, query_spec) = self;
        let relation_snake = relation.to_case(Snake);
        let age_str = match query_spec.age {
            QueryAge::New => "new",
            QueryAge::Old => "old",
            QueryAge::All => "all",
        };
        write!(f, "{relation_snake}.iter_{age_str}")?;
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

fn display_pub_predicate_holds_fn<'a>(
    pred: Pred,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let rel = eqlog.pred_rel(pred).unwrap();
        let relation = identifiers.get(&eqlog.rel_name(rel).unwrap()).unwrap();
        let relation_snake = relation.to_case(Snake);

        let arity = type_list_vec(eqlog.arity(rel).unwrap(), eqlog);
        let rel_fn_args = arity
            .iter()
            .copied()
            .enumerate()
            .map(|(i, typ)| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let arg = format!("arg{}", i);
                    let typ_camel =
                        format!("{}", display_type(typ, eqlog, identifiers)).to_case(UpperCamel);
                    write!(f, ", mut {arg}: {typ_camel}")
                })
            })
            .format("");

        let canonicalize = arity
            .iter()
            .copied()
            .enumerate()
            .map(|(i, typ)| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let arg = format!("arg{}", i);
                    let typ_snake =
                        format!("{}", display_type(typ, eqlog, identifiers)).to_case(Snake);
                    writeln!(f, "{arg} = self.root_{typ_snake}({arg});")
                })
            })
            .format("");

        let rel_args0 = (0..arity.len()).map(|i| format!("arg{}", i)).format(", ");
        let rel_args1 = rel_args0.clone();
        let relation_camel = relation.to_case(UpperCamel);

        writedoc! {f, "
            /// Returns `true` if `{relation}({rel_args0})` holds.
            #[allow(dead_code)]
            pub fn {relation_snake}(&self{rel_fn_args}) -> bool {{
                {canonicalize}
                self.{relation_snake}.contains({relation_camel}({rel_args1}))
            }}
        "}
    })
}

fn display_pub_function_eval_fn<'a>(
    func: Func,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let dom = type_list_vec(eqlog.domain(func).unwrap(), eqlog);
        let cod = eqlog.codomain(func).unwrap();
        let cod_camel = identifiers
            .get(&eqlog.type_name(cod).unwrap())
            .unwrap()
            .to_case(UpperCamel);
        let cod_index = dom.len();

        let rel = eqlog.func_rel(func).unwrap();
        let relation_name = identifiers.get(&eqlog.rel_name(rel).unwrap()).unwrap();
        let relation_snake = relation_name.to_case(Snake);

        let func_args = dom
            .iter()
            .copied()
            .enumerate()
            .map(|(i, typ)| {
                FmtFn(move |f: &mut Formatter| {
                    let type_camel = identifiers
                        .get(&eqlog.type_name(typ).unwrap())
                        .unwrap()
                        .to_case(UpperCamel);
                    write!(f, ", mut arg{i}: {type_camel}")
                })
            })
            .format("");

        let canonicalize = dom
            .iter()
            .copied()
            .enumerate()
            .map(|(i, t)| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let type_snake = identifiers
                        .get(&eqlog.type_name(t).unwrap())
                        .unwrap()
                        .to_case(Snake);
                    write!(f, "arg{i} = self.root_{type_snake}(arg{i});")
                })
            })
            .format("\n");

        let query = QuerySpec {
            projections: (0..dom.len()).collect(),
            diagonals: BTreeSet::new(),
            age: QueryAge::All,
        };
        let iter = IterName(relation_name, &query);
        let args0 = (0..dom.len()).format_with(", ", |i, f| f(&format_args!("arg{i}")));
        let args1 = args0.clone();

        writedoc! {f, "
            /// Evaluates `{relation_name}({args0})`.
            #[allow(dead_code)]
            pub fn {relation_snake}(&self{func_args}) -> Option<{cod_camel}> {{
                {canonicalize}
                self.{iter}({args1}).next().map(|t| t.{cod_index})
            }}
        "}
    })
}

fn display_pub_iter_fn<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    let relation_name = identifiers.get(&eqlog.rel_name(rel).unwrap()).unwrap();
    let relation_snake = relation_name.to_case(Snake);

    FmtFn(move |f: &mut Formatter| -> Result {
        let arity = type_list_vec(eqlog.arity(rel).unwrap(), eqlog);

        let iter_item_type = match arity.as_slice() {
            [t] => {
                let type_name = eqlog.type_name(*t).unwrap();
                let type_camel = identifiers.get(&type_name).unwrap().to_case(UpperCamel);
                format!("{type_camel}")
            }
            ts => {
                let args = ts
                    .iter()
                    .copied()
                    .map(|t| {
                        let type_name = eqlog.type_name(t).unwrap();
                        let type_camel = identifiers.get(&type_name).unwrap().to_case(UpperCamel);
                        type_camel
                    })
                    .format_with(", ", |s, f| f(&format_args!("{}", s)));
                format!("({args})")
            }
        };

        let tuple_unpack = match arity.len() {
            0 => "|_| ()".to_string(),
            1 => "|t| t.0".to_string(),
            n => {
                let args = (0..n).format_with(", ", |i, f| f(&format_args!("t.{i}")));
                format!("|t| ({args})")
            }
        };

        let is_function = match eqlog.rel_case(rel) {
            RelCase::PredRel(_) => false,
            RelCase::FuncRel(_) => true,
        };

        let docstring = match (is_function, arity.len()) {
            (false, 0) => {
                formatdoc! {"
                    /// Returns an iterator that yields () if the `{relation_name}` predicate holds.
                "}
            }

            (false, 1) => {
                formatdoc! {"
                    /// Returns an iterator over elements satisfying the `{relation_name}` predicate.
                "}
            }
            (false, n) => {
                debug_assert!(n > 0);
                formatdoc! {"
                    /// Returns an iterator over tuples of elements satisfying the `{relation_name}` predicate.
                "}
            }
            (true, 0) => panic!("Functions cannot have empty arity"),
            (true, 1) => {
                formatdoc! {"
                    /// Returns an iterator that yields the `{relation_name}` constant.
                    /// The iterator may yield more than one element if the model is not closed.
                "}
            }
            (true, n) => {
                debug_assert!(n > 1);
                formatdoc! {"
                    /// Returns an iterator over tuples in the graph of the `{relation_name}` function.
                    /// The relation yielded by the iterator need not be functional if the model is not closed.
                "}
            }
        };

        writedoc! {f, "
            {docstring}
            #[allow(dead_code)]
            pub fn iter_{relation_snake}(&self) -> impl '_ + Iterator<Item={iter_item_type}> {{
                self.{relation_snake}.iter_all().map({tuple_unpack})
            }}
        "}
    })
}

fn display_pub_insert_relation<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let rel_name = identifiers.get(&eqlog.rel_name(rel).unwrap()).unwrap();
        let rel_snake = rel_name.to_case(Snake);
        let rel_camel = rel_name.to_case(UpperCamel);

        // Turn variables into refs to that we can use them from the closures passed to e.g. `map`.
        let rel_name = rel_name.as_str();
        let rel_snake = rel_snake.as_str();
        let rel_camel = rel_camel.as_str();

        let arity = type_list_vec(eqlog.arity(rel).unwrap(), eqlog);
        let rel_args: Vec<FlatVar> = (0..arity.len()).map(FlatVar).collect();

        let rel_fn_args = rel_args
            .iter()
            .copied()
            .zip(arity.iter().copied())
            .map(|(arg, typ)| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let arg = display_var(arg);
                    let type_camel = identifiers
                        .get(&eqlog.type_name(typ).unwrap())
                        .unwrap()
                        .to_case(UpperCamel);
                    write!(f, "mut {arg}: {type_camel}")
                })
            })
            .format(", ");

        let canonicalize = rel_args
            .iter()
            .copied()
            .zip(arity.iter().copied())
            .map(|(arg, typ)| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let arg = display_var(arg);
                    let type_snake = identifiers
                        .get(&eqlog.type_name(typ).unwrap())
                        .unwrap()
                        .to_case(Snake);
                    write!(f, "{arg} = self.{type_snake}_equalities.root({arg});")
                })
            })
            .format("\n");

        let update_weights = rel_args
            .iter()
            .copied()
            .zip(arity.iter().copied())
            .enumerate()
            .map(|(i, (arg, typ))| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let arg = display_var(arg);
                    let type_snake = identifiers
                        .get(&eqlog.type_name(typ).unwrap())
                        .unwrap()
                        .to_case(Snake);
                    writedoc! {f, "
                        let weight{i} = &mut self.{type_snake}_weights[{arg}.0 as usize];
                        *weight{i} = weight{i}.saturating_add({rel_camel}Table::WEIGHT);
                    "}
                })
            })
            .format("\n");

        let is_function = match eqlog.rel_case(rel) {
            RelCase::PredRel(_) => false,
            RelCase::FuncRel(_) => true,
        };

        let docstring = if is_function {
            let dom_len = arity.len() - 1;
            let func_args = rel_args[..dom_len]
                .iter()
                .copied()
                .map(display_var)
                .format(", ");
            let result = display_var(*rel_args.last().expect("func can't have empty arity"));
            formatdoc! {"
                /// Makes the equation `{rel_name}({func_args}) = {result}` hold.
            "}
        } else {
            let rel_args = rel_args.iter().copied().map(display_var).format(", ");
            formatdoc! {"
                /// Makes `{rel_name}({rel_args})` hold.
            "}
        };

        let rel_args = rel_args.iter().copied().map(display_var).format(", ");

        writedoc! {f, "
            {docstring}
            #[allow(dead_code)]
            pub fn insert_{rel_snake}(&mut self, {rel_fn_args}) {{
                {canonicalize}
                if self.{rel_snake}.insert({rel_camel}({rel_args})) {{
                    {update_weights}
                }}
            }}
        "}
    })
}

fn display_new_model_element<'a>(
    model_type: Type,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f: &mut Formatter| -> Result {
        let type_name = eqlog.type_name(model_type).unwrap();
        let type_camel = identifiers.get(&type_name).unwrap().to_case(UpperCamel);
        let type_snake = type_camel.to_case(Snake);

        writedoc! {f, "
            /// Adjoins a new element of type [{type_camel}].
            #[allow(dead_code)]
            pub fn new_{type_snake}(&mut self) -> {type_camel} {{
                let el = self.new_{type_snake}_internal();
                self.{type_snake}_models.insert(el, RefCell::new({type_camel}Model::new()));
                el
            }}
        "}?;
        Ok(())
    })
}

fn display_get_model_fns<'a>(
    model_type: Type,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let type_name = eqlog.type_name(model_type).unwrap();
        let type_camel = identifiers.get(&type_name).unwrap().to_case(UpperCamel);
        let type_snake = type_camel.to_case(Snake);

        writedoc! {f, "
            #[allow(dead_code)]
            pub fn get_{type_snake}_model(&self, el: {type_camel}) -> std::cell::Ref<{type_camel}Model> {{
                let el = self.root_{type_snake}(el);
                self.{type_snake}_models.get(&el).unwrap().borrow()
            }}

            #[allow(dead_code)]
            pub fn get_{type_snake}_model_mut(&mut self, el: {type_camel}) -> std::cell::RefMut<{type_camel}Model> {{
                let el = self.root_{type_snake}(el);
                self.{type_snake}_models.get_mut(&el).unwrap().borrow_mut()
            }}
        "}?;
        Ok(())
    })
}

fn display_new_enum_element<'a>(
    enum_type: Type,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f: &mut Formatter| -> Result {
        let enum_name = eqlog.type_name(enum_type).unwrap();
        let enum_camel = identifiers.get(&enum_name).unwrap().to_case(UpperCamel);
        let enum_snake = enum_camel.to_case(Snake);

        // Make enum_camel and enum_snake accessible in the filter_map closure below.
        let enum_camel = enum_camel.as_str();
        let enum_snake = enum_snake.as_str();

        let match_branches = eqlog
            .iter_ctor_decl()
            .filter_map(|(ctor, ctor_name, _)| {
                let ctor_sym_scope = eqlog.ctor_symbol_scope(ctor).unwrap();
                let ctor_func = eqlog.semantic_func(ctor_sym_scope, ctor_name).unwrap();
                let codomain = eqlog.codomain(ctor_func).unwrap();
                (eqlog.are_equal_type(enum_type, codomain).then_some(()))?;

                let ctor_snake = identifiers.get(&ctor_name).unwrap().to_case(Snake);
                let ctor_camel = ctor_snake.to_case(UpperCamel);

                let ctor_arg_types: Vec<Type> =
                    type_list_vec(eqlog.domain(ctor_func).unwrap(), eqlog);
                let ctor_vars = (0..ctor_arg_types.len())
                    .map(|i| display_var(FlatVar(i)))
                    .format(", ");
                let func_vars = ctor_vars.clone();

                Some(FmtFn(move |f: &mut Formatter| -> Result {
                    writedoc! {f, "
                        {enum_camel}Case::{ctor_camel}({ctor_vars}) => {{
                            self.define_{ctor_snake}({func_vars})
                        }}
                    "}
                }))
            })
            .format("");

        writedoc! {f, "
            /// Adjoins a new element of type [{enum_camel}].
            #[allow(dead_code)]
            pub fn new_{enum_snake}(&mut self, value: {enum_camel}Case) -> {enum_camel} {{
                match value {{
                    {match_branches}
                }}
            }}
        "}
    })
}

fn display_enum_cases_fn<'a>(
    enum_type: Type,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f: &mut Formatter| -> Result {
        let enum_name = eqlog.type_name(enum_type).unwrap();
        let enum_camel = identifiers.get(&enum_name).unwrap().to_case(UpperCamel);
        let enum_snake = enum_camel.to_case(Snake);

        // Make enum_camel and enum_snake accessible in the filter_map closure below.
        let enum_camel = enum_camel.as_str();
        let enum_snake = enum_snake.as_str();

        let ctor_value_iters = eqlog
            .iter_ctor_decl()
            .filter_map(|(ctor, ctor_ident, _)| {
                let ctor_sym_scope = eqlog.ctor_symbol_scope(ctor).unwrap();
                let ctor_func = eqlog.semantic_func(ctor_sym_scope, ctor_ident).unwrap();
                let codomain = eqlog.codomain(ctor_func).unwrap();
                (eqlog.are_equal_type(enum_type, codomain).then_some(()))?;

                let ctor_name = identifiers.get(&ctor_ident).unwrap();
                let ctor_name_snake = ctor_name.to_case(Snake);
                let ctor_name_camel = ctor_name.to_case(UpperCamel);

                let arg_num = type_list_vec(eqlog.domain(ctor_func).unwrap(), eqlog).len();

                let ctor_arg_vars = (0..arg_num).map(FlatVar);
                let result_var = FlatVar(arg_num);
                let tuple_vars = ctor_arg_vars.clone().chain(once(result_var));

                let ctor_arg_vars = ctor_arg_vars.map(display_var).format(", ");
                let result_var = display_var(result_var);
                let tuple_vars = tuple_vars.map(display_var).format(", ");

                Some(FmtFn(move |f: &mut Formatter| -> Result {
                    // TODO: We probably want to use an index insted of a linear search here.
                    // However, this function is not needed during the close method, so those
                    // indices should only exist when the host program uses this function, probably
                    // lazily. But we don't have machinery for index lifetimes yet.
                    writedoc! {f, "
                        .chain(self.iter_{ctor_name_snake}().filter_map(move |({tuple_vars})| {{
                            if el == {result_var} {{
                                Some({enum_camel}Case::{ctor_name_camel}({ctor_arg_vars}))
                            }} else {{
                                None
                            }}
                        }}))
                    "}
                }))
            })
            .format("\n");

        // We need to allow the unused parens here in case of nullary constructors. For those, the
        // iter_{ctor_name_snake} function yields elements instead of tuples, but the argument to
        // the closure we pass to filter_map above still has parens around the single variable.
        writedoc! {f, "
            /// Returns an iterator over ways to destructure an [{enum_camel}] element.
            #[allow(dead_code)]
            pub fn {enum_snake}_cases<'a>(&'a self, el: {enum_camel}) -> impl 'a + Iterator<Item = {enum_camel}Case> {{
            let el = self.{enum_snake}_equalities.root_const(el);
            #[allow(unused_parens)]
            [].into_iter(){ctor_value_iters}
            }}

            /// Returns the first way to destructure an [{enum_camel}] element.
            #[allow(dead_code)]
            pub fn {enum_snake}_case(&self, el: {enum_camel}) -> {enum_camel}Case {{
                self.{enum_snake}_cases(el).next().unwrap()
            }}
        "}
    })
}

fn write_canonicalize_rel_block(
    out: &mut Formatter,
    // The symbol scope in which the relation is defined.
    symbol_scope: SymbolScope,
    rel: Rel,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> Result {
    let rel_snake = display_rel(rel, eqlog, identifiers)
        .to_string()
        .to_case(Snake);
    let rel_camel = rel_snake.to_case(UpperCamel);
    let rel_camel = rel_camel.as_str();

    let arity = type_list_vec(eqlog.arity(rel).unwrap(), eqlog);

    for typ in arity.iter().copied() {
        let type_symbol_scope = eqlog
            .type_definition_symbol_scope(typ)
            .expect("Every type should have been defined somehwere");
        let type_snake = display_type(typ, eqlog, identifiers)
            .to_string()
            .to_case(Snake);

        let type_symbol_scope_var = if eqlog.are_equal_symbol_scope(type_symbol_scope, symbol_scope)
        {
            "self".to_string()
        } else {
            display_symbol_scope_name(type_symbol_scope, eqlog, identifiers)
                .to_string()
                .to_case(Snake)
        };

        let canonicalize_ts = arity
            .iter()
            .copied()
            .enumerate()
            .map(|(i, type_i)| {
                let type_i_snake = display_type(type_i, eqlog, identifiers)
                    .to_string()
                    .to_case(Snake);
                let type_i_symbol_scope = eqlog
                    .type_definition_symbol_scope(type_i)
                    .expect("Every type should have been defined somehwere");
                let type_i_symbol_scope_var =
                    if eqlog.are_equal_symbol_scope(type_i_symbol_scope, symbol_scope) {
                        "self".to_string()
                    } else {
                        display_symbol_scope_name(type_i_symbol_scope, eqlog, identifiers)
                            .to_string()
                            .to_case(Snake)
                    };
                FmtFn(move |f| {
                    write!(
                        f,
                        "t.{i} = {type_i_symbol_scope_var}.root_{type_i_snake}(t.{i});"
                    )
                })
            })
            .format("\n");

        let adjust_weights = |op: &'static str| {
            arity
                .iter()
                .copied()
                .enumerate()
                .map(move |(i, type_i)| FmtFn(move |f| {
                    let type_i_snake = display_type(type_i, eqlog, identifiers).to_string().to_case(Snake);
                    let type_i_symbol_scope = eqlog.type_definition_symbol_scope(type_i).expect("Every type should have been defined somehwere");
                    let type_i_symbol_scope_var =
                        if eqlog.are_equal_symbol_scope(type_i_symbol_scope, symbol_scope) {
                            "self".to_string()
                        } else {
                            display_symbol_scope_name(type_i_symbol_scope, eqlog, identifiers).to_string().to_case(Snake)
                        };
                    writedoc! {f, "
                        let weight{i} = &mut {type_i_symbol_scope_var}.{type_i_snake}_weights[t.{i}.0 as usize];
                        *weight{i} = weight{i}.saturating_{op}({rel_camel}Table::WEIGHT);
                    "}
                }))
                .format("\n")
        };
        let reduce_weights = adjust_weights("sub");
        let increase_weights = adjust_weights("add");

        writedoc! {out, "
            for el in {type_symbol_scope_var}.{type_snake}_uprooted.iter().copied() {{
                let ts = self.{rel_snake}.drain_with_element_{type_snake}(el);
                for mut t in ts {{
                    {reduce_weights}
                    {canonicalize_ts}
                    if self.{rel_snake}.insert(t) {{
                        {increase_weights}
                    }}
                }}
            }}
        "}?;
    }
    Ok(())
}

fn display_canonicalize_fn<'a>(
    sym_scope: SymbolScope,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let ancestor_params = iter_symbol_scope_ancestors(sym_scope, eqlog)
            .map(|ancestor| {
                FmtFn(move |f| {
                    let type_name = display_symbol_scope_name(ancestor, eqlog, identifiers);
                    let var_name = type_name.to_string().to_case(Snake);
                    write!(f, "{var_name}: &mut {type_name}")
                })
            })
            .format(", ");
        let rel_blocks = iter_symbol_scope_relations(sym_scope, eqlog)
            .map(|rel| {
                FmtFn(move |f| write_canonicalize_rel_block(f, sym_scope, rel, eqlog, identifiers))
            })
            .format("\n");

        let merge_models = iter_symbol_scope_types(sym_scope, eqlog)
            .filter(|typ| eqlog.is_model_type(*typ))
            .map(|typ| {
                FmtFn(move |f| {
                    let type_snake = display_type(typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    writedoc! {f, "
                    for child in self.{type_snake}_uprooted.iter().copied() {{
                        let root = self.{type_snake}_equalities.root(child);

                        let child_model = self.{type_snake}_models.remove(&child).unwrap().into_inner();
                        let root_model = self.{type_snake}_models.get_mut(&root).unwrap().get_mut();
                        root_model.merge(child_model);
                    }}
                "}
                })
            })
            .format("\n");

        let clear_uprooted_vecs = iter_symbol_scope_types(sym_scope, eqlog)
            .map(|typ| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let type_snake =
                        format!("{}", display_type(typ, eqlog, identifiers)).to_case(Snake);
                    write!(f, "self.{type_snake}_uprooted.clear();")
                })
            })
            .format("\n");

        let nested_model_canonicalize = iter_symbol_scope_types(sym_scope, eqlog)
            .filter_map(|typ| {
                eqlog.is_model_type(typ).then_some(())?;
                Some(FmtFn(move |f: &mut Formatter| -> Result {
                    let type_snake = display_type(typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    let sym_scope_params = iter_symbol_scope_ancestors(sym_scope, eqlog)
                        .map(|ancestor| {
                            FmtFn(move |f| {
                                let type_name =
                                    display_symbol_scope_name(ancestor, eqlog, identifiers);
                                let var_name = type_name.to_string().to_case(Snake);
                                write!(f, ", {var_name}")
                            })
                        })
                        .format("");

                    // TODO: We need to to the swapping here because we can't borrow self mutably.
                    // It'd be better if we didn't have to pass through all of `self` but instead
                    // only those parts that are needed.
                    writedoc! {f, "
                        let mut models_map = BTreeMap::new();
                        std::mem::swap(&mut models_map, &mut self.{type_snake}_models);
                        for model in models_map.values_mut() {{
                            model.get_mut().canonicalize(self {sym_scope_params});
                        }}
                        std::mem::swap(&mut models_map, &mut self.{type_snake}_models);
                    "}
                }))
            })
            .format("\n");

        writedoc! {f, "
            fn canonicalize(&mut self, {ancestor_params}) {{
                {rel_blocks}

                {merge_models}

                {clear_uprooted_vecs}

                {nested_model_canonicalize}
            }}
        "}
    })
}

fn display_symbol_scope_delta_struct<'a>(
    sym_scope: SymbolScope,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    let delta_name = display_symbol_scope_delta_name(sym_scope, eqlog, identifiers);
    FmtFn(move |f: &mut Formatter| -> Result {
        writedoc! {f, "
            #[derive(Debug, Clone)]
            struct {delta_name} {{
        "}?;

        for typ in iter_symbol_scope_types(sym_scope, eqlog) {
            let name_snake = identifiers
                .get(&eqlog.type_name(typ).unwrap())
                .unwrap()
                .as_str()
                .to_case(Snake);
            let name_camel = name_snake.to_case(UpperCamel);
            writeln!(
                f,
                "new_{name_snake}_equalities: Vec<({name_camel}, {name_camel})>,"
            )?;

            if eqlog.is_model_type(typ) {
                let member_sym_scope = eqlog.model_member_symbol_scope(typ).unwrap();
                let delta_name =
                    display_symbol_scope_delta_name(member_sym_scope, eqlog, identifiers);
                writedoc! {f, "
                    {name_snake}_deltas: BTreeMap<{name_camel}, {delta_name}>,
                "}?;
            }
        }

        for rel in iter_symbol_scope_relations(sym_scope, eqlog) {
            let name_snake = identifiers
                .get(&eqlog.rel_name(rel).unwrap())
                .unwrap()
                .as_str()
                .to_case(Snake);
            let name_camel = name_snake.to_case(UpperCamel);
            writeln!(f, "new_{name_snake}: Vec<{name_camel}>,")?;

            if let RelCase::FuncRel(func) = eqlog.rel_case(rel) {
                if eqlog.function_can_be_made_defined(func) {
                    writeln!(f, "new_{name_snake}_def: Vec<{name_camel}Args>,")?;
                }
            }
        }

        writeln!(f, "}}\n")?;

        Ok(())
    })
}

fn display_symbol_scope_delta_impl<'a>(
    sym_scope: SymbolScope,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    let model_name = display_symbol_scope_name(sym_scope, eqlog, identifiers);
    let delta_name = display_symbol_scope_delta_name(sym_scope, eqlog, identifiers);

    FmtFn(move |f: &mut Formatter| -> Result {
        let new_fn = display_model_delta_new_fn(sym_scope, eqlog, identifiers);
        // TODO: Why does this trigger the `unused` warning? It's used in the format string below.
        #[allow(unused)]
        let apply_equalities_fn =
            display_model_delta_apply_equalities_fn(sym_scope, eqlog, identifiers);
        let apply_tuples_fn = display_model_delta_apply_tuples_fn(sym_scope, eqlog, identifiers);
        let apply_def_fn = display_model_delta_apply_def_fn(sym_scope, eqlog, identifiers);
        let apply_nested_surjective_fn =
            display_model_delta_apply_nested_surjective_fn(sym_scope, eqlog, identifiers);
        let apply_nested_non_surjective_fn =
            display_model_delta_apply_nested_non_surjective_fn(sym_scope, eqlog, identifiers);
        writedoc! {f, "
            impl {delta_name} {{
            {new_fn}

            fn apply_surjective(&mut self, model: &mut {model_name}) {{
                self.apply_nested_surjective(model);
                self.apply_equalities(model);
                self.apply_tuples(model);
            }}
            fn apply_non_surjective(&mut self, model: &mut {model_name}) {{
                self.apply_nested_non_surjective(model);
                self.apply_func_defs(model);
            }}

            {apply_equalities_fn}
            {apply_tuples_fn}
            {apply_def_fn}

            {apply_nested_surjective_fn}
            {apply_nested_non_surjective_fn}
            }}
        "}
    })
}

fn display_model_delta_new_fn<'a>(
    sym_scope: SymbolScope,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let new_equalities = iter_symbol_scope_types(sym_scope, eqlog)
            .map(|typ| {
                let type_name = eqlog.type_name(typ).unwrap();
                FmtFn(move |f: &mut Formatter| -> Result {
                    let name_snake = identifiers.get(&type_name).unwrap().as_str().to_case(Snake);
                    write!(f, "new_{name_snake}_equalities: Vec::new(),")?;

                    if eqlog.is_model_type(typ) {
                        writedoc! {f, "
                            {name_snake}_deltas: BTreeMap::new(),
                        "}?;
                    }
                    Ok(())
                })
            })
            .format("\n");

        let new_tuples_and_defs = iter_symbol_scope_relations(sym_scope, eqlog)
            .map(|rel| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let name_snake = identifiers
                        .get(&eqlog.rel_name(rel).unwrap())
                        .unwrap()
                        .as_str()
                        .to_case(Snake);
                    writeln!(f, "new_{name_snake}: Vec::new(),")?;
                    if let RelCase::FuncRel(func) = eqlog.rel_case(rel) {
                        if eqlog.function_can_be_made_defined(func) {
                            writeln!(f, "new_{name_snake}_def: Vec::new(),")?;
                        }
                    }
                    Ok(())
                })
            })
            .format("");

        writedoc! {f, "
            fn new() -> Self {{
            Self {{
            {new_tuples_and_defs}
            {new_equalities}
            }}
            }}
        "}
    })
}

fn display_model_delta_apply_equalities_fn<'a>(
    sym_scope: SymbolScope,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    let model_name = display_symbol_scope_name(sym_scope, eqlog, identifiers);
    FmtFn(move |f: &mut Formatter| -> Result {
        let type_equalities = iter_symbol_scope_types(sym_scope, eqlog)
            .map(|typ| {
                let type_name = eqlog.type_name(typ).unwrap();
                FmtFn(move |f: &mut Formatter| -> Result {
                    let type_snake = identifiers.get(&type_name).unwrap().as_str().to_case(Snake);
                    writedoc! {f, "
                        for (lhs, rhs) in self.new_{type_snake}_equalities.drain(..) {{
                            model.equate_{type_snake}(lhs, rhs);
                        }}
                    "}
                })
            })
            .format("\n");

        writedoc! {f, "
            #[allow(unused)]
            fn apply_equalities(&mut self, model: &mut {model_name}) {{
            {type_equalities}
            }}
        "}
    })
}

fn display_model_delta_apply_tuples_fn<'a>(
    sym_scope: SymbolScope,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    let model_name = display_symbol_scope_name(sym_scope, eqlog, identifiers);
    FmtFn(move |f: &mut Formatter| -> Result {
        let relations = iter_symbol_scope_relations(sym_scope, eqlog)
            .map(|rel| {
                let relation_snake = identifiers
                    .get(&eqlog.rel_name(rel).unwrap())
                    .unwrap()
                    .as_str()
                    .to_case(Snake);
                let relation_camel = relation_snake.to_case(UpperCamel);

                let arity = type_list_vec(eqlog.arity(rel).unwrap(), eqlog);

                let args0 = (0..arity.len()).map(FlatVar).map(display_var).format(", ");
                let args1 = args0.clone();

                FmtFn(move |f: &mut Formatter| -> Result {
                    writedoc! {f, "
                        for {relation_camel}({args0}) in self.new_{relation_snake}.drain(..) {{
                            model.insert_{relation_snake}({args1});
                        }}
                    "}?;
                    Ok(())
                })
            })
            .format("\n");

        writedoc! {f, "
            #[allow(unused_variables)]
            fn apply_tuples(&mut self, model: &mut {model_name}) {{
                {relations}
            }}
        "}
    })
}

fn display_model_delta_apply_def_fn<'a>(
    sym_scope: SymbolScope,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let model_name = display_symbol_scope_name(sym_scope, eqlog, identifiers);
        let func_defs = iter_symbol_scope_relations(sym_scope, eqlog)
            .filter_map(|rel| {
                let func = match eqlog.rel_case(rel) {
                    RelCase::FuncRel(func) => func,
                    _ => return None,
                };
                eqlog.function_can_be_made_defined(func).then_some(())?;
                let func_snake = identifiers
                    .get(&eqlog.rel_name(rel).unwrap())
                    .unwrap()
                    .as_str()
                    .to_case(Snake);
                let func_camel = func_snake.to_case(UpperCamel);

                let domain = type_list_vec(eqlog.domain(func).unwrap(), eqlog);
                let args0 = (0..domain.len()).map(FlatVar).map(display_var).format(", ");
                let args1 = args0.clone();

                Some(FmtFn(move |f: &mut Formatter| -> Result {
                    writedoc! {f, "
                            for {func_camel}Args({args0}) in self.new_{func_snake}_def.drain(..) {{
                                model.define_{func_snake}({args1});
                            }}
                        "}
                }))
            })
            .format("\n");

        writedoc! {f, "
            #[allow(unused_variables)]
            fn apply_func_defs(&mut self, model: &mut {model_name}) {{
                {func_defs}
            }}
        "}
    })
}

fn display_model_delta_apply_nested_surjective_fn<'a>(
    sym_scope: SymbolScope,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    let model_name = display_symbol_scope_name(sym_scope, eqlog, identifiers);
    FmtFn(move |f: &mut Formatter| -> Result {
        let nested_apply_loops = iter_symbol_scope_types(sym_scope, eqlog)
            .filter_map(|typ| {
                (eqlog.is_model_type(typ)).then_some(())?;

                let type_snake = identifiers
                    .get(&eqlog.type_name(typ).unwrap())
                    .unwrap()
                    .to_case(Snake);
                Some(FmtFn(move |f: &mut Formatter| -> Result {
                    writedoc! {f, "
                        for (el, nested_delta) in self.{type_snake}_deltas.iter_mut() {{
                        let nested_model = model.{type_snake}_models.get_mut(el).unwrap().get_mut();
                        nested_delta.apply_surjective(nested_model);
                        }}
                    "}
                }))
            })
            .format("\n");

        writedoc! {f, "
            #[allow(unused_variables)]
            fn apply_nested_surjective(&mut self, model: &mut {model_name}) {{
            {nested_apply_loops}
            }}
        "}
    })
}

fn display_model_delta_apply_nested_non_surjective_fn<'a>(
    sym_scope: SymbolScope,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    let model_name = display_symbol_scope_name(sym_scope, eqlog, identifiers);
    FmtFn(move |f: &mut Formatter| -> Result {
        let nested_apply_loops = iter_symbol_scope_types(sym_scope, eqlog)
            .filter_map(|typ| {
                (eqlog.is_model_type(typ)).then_some(())?;

                let type_snake = identifiers
                    .get(&eqlog.type_name(typ).unwrap())
                    .unwrap()
                    .to_case(Snake);
                Some(FmtFn(move |f: &mut Formatter| -> Result {
                    writedoc! {f, "
                        for (el, nested_delta) in self.{type_snake}_deltas.iter_mut() {{
                        let nested_model = model.{type_snake}_models.get_mut(el).unwrap().get_mut();
                        nested_delta.apply_non_surjective(nested_model);
                        }}
                    "}
                }))
            })
            .format("\n");

        writedoc! {f, "
            #[allow(unused_variables)]
            fn apply_nested_non_surjective(&mut self, model: &mut {model_name}) {{
            {nested_apply_loops}
            }}
        "}
    })
}

fn display_var(var: FlatVar) -> impl Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let var = var.0;
        write!(f, "tm{var}")?;
        Ok(())
    })
}

fn display_type<'a>(
    typ: Type,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    let ident = eqlog
        .iter_semantic_type()
        .find_map(|(_scope, ident, typ0)| eqlog.are_equal_type(typ0, typ).then_some(ident))
        .expect("semantic_type should be surjective");
    identifiers.get(&ident).unwrap().as_str()
}

fn display_if_stmt_header<'a>(
    stmt: &'a FlatIfStmt,
    analysis: &'a FlatRuleAnalysis<'a>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        match stmt {
            FlatIfStmt::Equal(eq_stmt) => {
                let FlatStmtEqual { lhs, rhs } = eq_stmt;

                let FlatType {
                    local_type: typ,
                    model,
                } = *analysis.var_types.get(lhs).unwrap();
                if model.is_some() {
                    todo!("model member type in if stmts")
                }
                let typ = format!("{}", display_type(typ, eqlog, identifiers));
                let type_snake = typ.to_case(Snake);

                let lhs = display_var(*lhs);
                let rhs = display_var(*rhs);

                writedoc! {f, "
                    if self.are_equal_{type_snake}({lhs}.var, {rhs}.var) {{
                "}?;
            }
            FlatIfStmt::Relation(rel_stmt) => {
                let FlatIfStmtRelation {
                    rel,
                    args,
                    age,
                    model,
                } = rel_stmt;
                let RelationInfo {
                    diagonals,
                    in_projections,
                    out_projections,
                } = analysis
                    .if_stmt_rel_infos
                    .get(&ByAddress(rel_stmt))
                    .unwrap();
                let arity_len = args.len();
                let query_spec = QuerySpec {
                    diagonals: diagonals.clone(),
                    projections: in_projections.keys().copied().collect(),
                    age: *age,
                };
                let relation = format!("{}", display_rel(*rel, eqlog, identifiers));
                let relation_camel = relation.to_case(UpperCamel);
                write!(f, "#[allow(unused_variables)]\n")?;
                write!(f, "for {relation_camel}(")?;
                for i in 0..arity_len {
                    if let Some(var) = out_projections.get(&i) {
                        write!(f, "tm{}", var.0)?;
                    } else {
                        write!(f, "_")?;
                    }
                    write!(f, ", ")?;
                }
                match *model {
                    None => {
                        write!(f, ") in self.")?;
                    }
                    Some(model) => {
                        let model_var = display_var(model);
                        let model_type = analysis.var_types.get(&model).unwrap();
                        let model_type_snake =
                            display_type(model_type.local_type, eqlog, identifiers)
                                .to_string()
                                .to_case(Snake);
                        write!(
                            f,
                            ") in {model_var}.get_model(&self.{model_type_snake}_models)."
                        )?;
                    }
                }
                let iter_name = IterName(relation.as_str(), &query_spec);
                write!(f, "{iter_name}")?;
                write!(f, "(")?;
                for tm in in_projections.values().copied() {
                    write!(f, "tm{}.var, ", tm.0)?;
                }
                write!(f, ") {{\n")?;
                for tm in out_projections.values().copied() {
                    let var = display_var(tm);
                    let FlatType {
                        local_type: typ,
                        model: _,
                    } = *analysis.var_types.get(&tm).unwrap();
                    let var_type = display_var_type(typ, eqlog, identifiers);
                    writedoc! {f, "
                        #[allow(unused_mut)]
                        let mut {var} = {var_type}::new({var});
                    "}?;
                }
            }
            FlatIfStmt::Type(type_stmt) => {
                let FlatIfStmtType { var, age, var_type } = type_stmt;
                let FlatType {
                    local_type: typ,
                    model,
                } = *var_type;
                let type_snake = identifiers
                    .get(&eqlog.type_name(typ).unwrap())
                    .unwrap()
                    .to_case(Snake);
                let access_expr = FmtFn(|f: &mut Formatter| {
                    match model {
                        Some(model) => {
                            let FlatType {
                                local_type: model_type,
                                model: _,
                            } = *analysis.var_types.get(&model).unwrap();
                            let model_type_snake = identifiers
                                .get(&eqlog.type_name(model_type).unwrap())
                                .unwrap()
                                .to_case(Snake);
                            let model_var = display_var(model);
                            write!(f, "{model_var}.get_model(&self.{model_type_snake}_models)")?;
                        }
                        None => {
                            write!(f, "self")?;
                        }
                    }
                    Ok(())
                });
                let var = display_var(*var);
                match age {
                    QueryAge::New => {
                        writedoc! {f, "
                            #[allow(unused_variables)]
                            for {var} in {access_expr}.{type_snake}_new.iter().copied() {{
                        "}?;
                    }
                    QueryAge::Old => {
                        writedoc! {f, "
                            #[allow(unused_variables)]
                            for {var} in {access_expr}.{type_snake}_old.iter().copied() {{
                        "}?;
                    }
                    QueryAge::All => {
                        writedoc! {f, "
                            #[allow(unused_variables)]
                            for {var} in {access_expr}.{type_snake}_old.iter().chain({access_expr}.{type_snake}_new.iter()).copied() {{
                        "}?;
                    }
                }
                let var_type = display_var_type(typ, eqlog, identifiers);
                writedoc! {f, "
                    #[allow(unused_mut)]
                    let mut {var} = {var_type}::new({var});
                "}?;
            }
        };

        Ok(())
    })
}

fn display_surj_then<'a>(
    stmt: &'a FlatSurjThenStmt,
    analysis: &'a FlatRuleAnalysis<'a>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        match stmt {
            FlatSurjThenStmt::Equal(eq_stmt) => {
                let FlatStmtEqual { lhs, rhs } = eq_stmt;

                let FlatType { local_type, model } = *analysis.var_types.get(lhs).unwrap();
                let local_type_snake = display_type(local_type, eqlog, identifiers)
                    .to_string()
                    .to_case(Snake);

                let delta = FmtFn(move |f: &mut Formatter| -> Result {
                    match model {
                        None => {
                            write!(f, "delta")?;
                        }
                        Some(model) => {
                            let FlatType {
                                local_type: model_type,
                                model: iterated_model,
                            } = *analysis.var_types.get(&model).unwrap();
                            if iterated_model.is_some() {
                                todo!("Nested model types");
                            }
                            let model_type_snake = display_type(model_type, eqlog, identifiers)
                                .to_string()
                                .to_case(Snake);
                            let model_type_camel = model_type_snake.to_case(UpperCamel);
                            let model_var = display_var(model);
                            writedoc! {f,
                                "delta
                                .{model_type_snake}_deltas
                                .entry({model_var}.var)
                                .or_insert_with(|| {model_type_camel}ModelDelta::new())
                            "}?;
                        }
                    }
                    Ok(())
                });

                let lhs = display_var(*lhs);
                let rhs = display_var(*rhs);

                writedoc! {f, "
                    {delta}
                    .new_{local_type_snake}_equalities
                    .push(({lhs}.var, {rhs}.var));
                "}?;
            }
            FlatSurjThenStmt::Relation(rel_stmt) => {
                let FlatSurjThenStmtRelation { rel, args } = rel_stmt;
                let relation_camel =
                    format!("{}", display_rel(*rel, eqlog, identifiers)).to_case(UpperCamel);
                let relation_snake =
                    format!("{}", display_rel(*rel, eqlog, identifiers)).to_case(Snake);
                let args0 = args
                    .iter()
                    .copied()
                    .map(|arg| {
                        FmtFn(move |f: &mut Formatter| -> Result {
                            let var = display_var(arg);
                            write!(f, "{var}.var")
                        })
                    })
                    .format(", ");
                let args1 = args0.clone();
                let query_spec = QuerySpec {
                    projections: (0..args.len()).collect(),
                    diagonals: BTreeSet::new(),
                    age: QueryAge::All,
                };
                let iter_name = IterName(relation_camel.as_str(), &query_spec);
                writedoc! {f, "
                    let exists_already = self.{iter_name}({args0}).next().is_some();
                    if !exists_already {{
                    delta.new_{relation_snake}.push({relation_camel}({args1}));
                    }}
                "}?;
            }
        };

        Ok(())
    })
}

fn display_non_surj_then<'a>(
    stmt: &'a FlatNonSurjThenStmt,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let FlatNonSurjThenStmt {
            func,
            func_args,
            result,
        } = stmt;
        let rel = eqlog.func_rel(*func).unwrap();
        let relation_camel =
            format!("{}", display_rel(rel, eqlog, identifiers)).to_case(UpperCamel);
        let relation_snake = format!("{}", display_rel(rel, eqlog, identifiers)).to_case(Snake);

        let eval_func_spec = QuerySpec::eval_func(*func, eqlog);
        let iter_name = IterName(relation_camel.as_str(), &eval_func_spec);

        let in_args0 = func_args
            .iter()
            .copied()
            .map(|var| {
                let var = display_var(var);
                FmtFn(move |f: &mut Formatter| -> Result { write!(f, "{var}.var") })
            })
            .format(", ");
        let in_args1 = in_args0.clone();

        let out_arg_wildcards = repeat("_, ").take(func_args.len()).format("");
        let result = display_var(*result);

        let result_var_type = display_var_type(eqlog.codomain(*func).unwrap(), eqlog, identifiers);

        writedoc! {f, "
            #[allow(unused_mut)]
            let mut {result} = match self.{iter_name}({in_args0}).next() {{
                Some({relation_camel}({out_arg_wildcards} res)) => {result_var_type}::new(res),
                None => {{ 
                    delta.new_{relation_snake}_def.push({relation_camel}Args({in_args1}));
                    break;
                }},
            }};
        "}?;
        Ok(())
    })
}

fn display_stmts<'a>(
    stmts: &'a [FlatStmt],
    analysis: &'a FlatRuleAnalysis<'a>,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let (head, tail) = match stmts {
            [] => {
                return Ok(());
            }
            [head, tail @ ..] => (head, tail),
        };

        match head {
            FlatStmt::If(if_stmt) => {
                let if_header = display_if_stmt_header(if_stmt, analysis, eqlog, identifiers);
                let if_footer = "}";
                let tail = display_stmts(tail, analysis, eqlog, identifiers);
                writedoc! {f, "
                    {if_header}
                    {tail}
                    {if_footer}
                "}?;
            }
            FlatStmt::SurjThen(surj_then) => {
                let tail = display_stmts(tail, analysis, eqlog, identifiers);
                let surj_then = display_surj_then(surj_then, analysis, eqlog, identifiers);
                writedoc! {f, "
                    {surj_then}
                    {tail}
                "}?;
            }
            FlatStmt::NonSurjThen(non_surj_then) => {
                let tail = display_stmts(tail, analysis, eqlog, identifiers);
                let non_surj_then = display_non_surj_then(non_surj_then, eqlog, identifiers);
                writedoc! {f, "
                    {non_surj_then}
                    {tail}
                "}?;
            }
            FlatStmt::Call { func_name, args } => {
                let rule_name = analysis.rule_name;
                let i = func_name.0;
                let args = args.iter().copied().map(display_var).format(", ");
                let tail = display_stmts(tail, analysis, eqlog, identifiers);
                writedoc! {f, "
                    self.{rule_name}_{i}(delta, {args});
                    {tail}
                "}?;
            }
        };
        Ok(())
    })
}

fn display_rule_func<'a>(
    rule_name: &'a str,
    flat_func: &'a FlatFunc,
    analysis: &'a FlatRuleAnalysis<'a>,
    module: ModuleNode,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    let func_name = flat_func.name.0;

    let var_args = flat_func
        .args
        .iter()
        .copied()
        .map(|var| {
            let var_name = display_var(var);
            let FlatType {
                local_type: typ,
                model: _,
            } = *analysis.var_types.get(&var).unwrap();
            let var_type = display_var_type(typ, eqlog, identifiers);
            FmtFn(move |f: &mut Formatter| -> Result {
                write!(f, "mut {var_name}: {var_type}<'a>")
            })
        })
        .format(", ");

    let stmts = display_stmts(flat_func.body.as_slice(), analysis, eqlog, identifiers);

    let module_sym_scope = eqlog.module_symbol_scope(module).unwrap();
    let delta_name = display_symbol_scope_delta_name(module_sym_scope, eqlog, identifiers);

    FmtFn(move |f: &mut Formatter| -> Result {
        writedoc! {f, "
            #[allow(unused_variables, unused_mut)]
            fn {rule_name}_{func_name}<'a>(&'a self, delta: &mut {delta_name}, {var_args}) {{
            for _ in [()] {{
            {stmts}
            }}
            }}
        "}
    })
}

fn display_rule_fns<'a>(
    rule: &'a FlatRule,
    analysis: &'a FlatRuleAnalysis<'a>,
    module: ModuleNode,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let funcs = rule
            .funcs
            .iter()
            .map(|func| {
                display_rule_func(
                    rule.name.as_str(),
                    func,
                    analysis,
                    module,
                    eqlog,
                    identifiers,
                )
            })
            .format("\n");
        writeln!(f, "{}", funcs)?;
        Ok(())
    })
}

fn write_close_until_fn(
    out: &mut impl Write,
    module: ModuleNode,
    rules: &[FlatRule],
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> io::Result<()> {
    let rules = rules
        .iter()
        .map(|rule| {
            FmtFn(move |f: &mut Formatter| -> Result {
                let name = rule.name.as_str();
                write!(f, "self.{name}_0(&mut delta);")
            })
        })
        .format("\n");

    let module_sym_scope = eqlog.module_symbol_scope(module).unwrap();
    let module_name = eqlog.symbol_scope_name(module_sym_scope).unwrap();
    let module_camel = identifiers
        .get(&module_name)
        .unwrap()
        .as_str()
        .to_case(UpperCamel);

    writedoc! {out, "
        /// Closes the model under all axioms until `condition` is satisfied.
        /// Depending on the axioms and `condition`, this may run indefinitely.
        /// Returns `true` if the `condition` eventually holds.
        /// Returns `false` if the model could be closed under all axioms but `condition` still does not hold.
        #[allow(dead_code)]
        pub fn close_until(&mut self, condition: impl Fn(&Self) -> bool) -> bool
        {{
            let mut delta = {module_camel}Delta::new();

            self.canonicalize();
            if condition(self) {{
                return true;
            }}

            while self.is_dirty() {{
                loop {{
        {rules}

                    self.drop_dirt();
                    delta.apply_surjective(self);
                    self.canonicalize();

                    if condition(self) {{
                        return true;
                    }}

                    if !self.is_dirty() {{
                        break;
                    }}
                }}

                delta.apply_non_surjective (self);
                if condition(self) {{
                    return true;
                }}
            }}

            false
        }}
    "}
}

fn display_drop_dirt_fn<'a>(
    sym_scope: SymbolScope,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let relations = iter_symbol_scope_relations(sym_scope, eqlog)
            .map(|rel| {
                let relation_snake = identifiers
                    .get(&eqlog.rel_name(rel).unwrap())
                    .unwrap()
                    .as_str()
                    .to_case(Snake);
                FmtFn(move |f: &mut Formatter| -> Result {
                    write!(f, "self.{relation_snake}.drop_dirt();")
                })
            })
            .format("\n");

        let sorts = iter_symbol_scope_types(sym_scope, eqlog)
            .map(|typ| {
                let sort_snake = identifiers
                    .get(&eqlog.type_name(typ).unwrap())
                    .unwrap()
                    .as_str()
                    .to_case(Snake);
                FmtFn(move |f: &mut Formatter| -> Result {
                    writedoc! { f, "
                        self.{sort_snake}_old.append(&mut self.{sort_snake}_new);
                    "}?;
                    if eqlog.is_model_type(typ) {
                        writedoc! { f, "
                            for model in self.{sort_snake}_models.values_mut() {{
                                model.get_mut().drop_dirt();
                            }}
                        "}?;
                    }
                    Ok(())
                })
            })
            .format("");

        writedoc! {f, "
            fn drop_dirt(&mut self) {{
                self.empty_join_is_dirty = false;

                {relations}

                {sorts}
            }}
        "}
    })
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

fn display_symbol_scope_new_fn<'a>(
    sym_scope: SymbolScope,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    let sym_scope_name = identifiers
        .get(&eqlog.symbol_scope_name(sym_scope).unwrap())
        .unwrap();

    FmtFn(move |f: &mut Formatter| -> Result {
        let is_module_sym_scope = eqlog.iter_module_node().any(|module| {
            eqlog.are_equal_symbol_scope(eqlog.module_symbol_scope(module).unwrap(), sym_scope)
        });

        let visibility = if is_module_sym_scope { "pub " } else { "" };

        writedoc! {f, "
            /// Creates an empty {sym_scope_name} model.
            #[allow(dead_code)]
            {visibility}fn new() -> Self {{
                Self {{
        "}?;

        for typ in iter_symbol_scope_types(sym_scope, eqlog) {
            let type_snake = identifiers
                .get(&eqlog.type_name(typ).unwrap())
                .unwrap()
                .as_str()
                .to_case(Snake);
            writedoc! {f, "
                {type_snake}_equalities: Unification::new(),
                {type_snake}_weights: Vec::new(),
                {type_snake}_new: BTreeSet::new(),
                {type_snake}_old: BTreeSet::new(),
                {type_snake}_uprooted: Vec::new(),
            "}?;

            if eqlog.is_model_type(typ) {
                writedoc! {f, "
                    {type_snake}_models: BTreeMap::new(),
                "}?;
            }
        }

        for rel in iter_symbol_scope_relations(sym_scope, eqlog) {
            let relation_snake = identifiers
                .get(&eqlog.rel_name(rel).unwrap())
                .unwrap()
                .as_str()
                .to_case(Snake);
            let relation_camel = relation_snake.to_case(UpperCamel);
            writedoc! {f, "
                {relation_snake}: {relation_camel}Table::new(),
            "}?;
        }

        writedoc! {f, "
                    empty_join_is_dirty: true,
                }}
            }}
        "}?;

        Ok(())
    })
}

fn display_define_fn<'a>(
    func: Func,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let func_snake = display_func_snake(func, eqlog, identifiers);

        let domain = type_list_vec(eqlog.domain(func).expect("should be total"), eqlog);
        let codomain = eqlog.codomain(func).expect("should be total");

        let codomain_camel =
            format!("{}", display_type(codomain, eqlog, identifiers)).to_case(UpperCamel);
        let codomain_snake = codomain_camel.to_case(Snake);

        let func_arg_vars: Vec<FlatVar> = (0..domain.len()).map(FlatVar).collect();
        let result_var = FlatVar(domain.len());

        let fn_args = func_arg_vars
            .iter()
            .copied()
            .zip(domain.iter().copied())
            .map(|(var, var_typ)| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let type_camel = format!("{}", display_type(var_typ, eqlog, identifiers))
                        .to_case(UpperCamel);
                    let var = display_var(var);
                    write!(f, "{var}: {type_camel}")
                })
            })
            .format(", ");

        let args0 = func_arg_vars.iter().copied().map(display_var).format(", ");
        let args1 = args0.clone();
        let rel_args = func_arg_vars
            .iter()
            .copied()
            .chain(once(result_var))
            .map(display_var)
            .format(", ");
        let result_var = display_var(result_var);

        writedoc! {f, "
            /// Enforces that `{func_snake}({args0})` is defined, adjoining a new element if necessary.
            #[allow(dead_code)]
            pub fn define_{func_snake}(&mut self, {fn_args}) -> {codomain_camel} {{
                match self.{func_snake}({args1}) {{
                    Some(result) => result,
                    None => {{
                        let {result_var} = self.new_{codomain_snake}_internal();
                        self.insert_{func_snake}({rel_args});
                        {result_var}
                    }}
                }}
            }}
        "}
    })
}

/// Displays a struct that holds data for all symbols defined in a [SymbolScope].
fn display_symbol_scope_struct<'a>(
    sym_scope: SymbolScope,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let model_name = display_symbol_scope_name(sym_scope, eqlog, identifiers);

        let type_fields = iter_symbol_scope_types(sym_scope, eqlog)
            .map(|typ| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let type_snake = identifiers
                        .get(&eqlog.type_name(typ).unwrap())
                        .unwrap()
                        .to_case(Snake);
                    let type_name = display_type(typ, eqlog, identifiers);
                    writedoc! {f, "
                        {type_snake}_equalities: Unification<{type_name}>,
                        {type_snake}_old: BTreeSet<{type_name}>,
                        {type_snake}_new: BTreeSet<{type_name}>,
                        {type_snake}_weights: Vec<usize>,
                        {type_snake}_uprooted: Vec<{type_name}>,
                    "}?;

                    if eqlog.is_model_type(typ) {
                        let member_sym_scope = eqlog.model_member_symbol_scope(typ).unwrap();
                        let model_sym_scope_name =
                            display_symbol_scope_name(member_sym_scope, eqlog, identifiers);
                        writedoc! {f, "
                            {type_snake}_models: BTreeMap<{type_name}, RefCell<{model_sym_scope_name}>>,
                        "}?;
                    }

                    Ok(())
                })
            })
            .format("");

        let relation_fields = iter_symbol_scope_relations(sym_scope, eqlog)
            .map(|rel| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let relation_snake = identifiers
                        .get(&eqlog.rel_name(rel).unwrap())
                        .unwrap()
                        .to_case(Snake);
                    let relation_camel = relation_snake.to_case(UpperCamel);
                    writedoc! {f, "
                        {relation_snake}: {relation_camel}Table,
                    "}
                })
            })
            .format("");

        writedoc! {f, "
            #[derive(Debug, Clone)]
            pub struct {model_name} {{
            {relation_fields}
            {type_fields}
            empty_join_is_dirty: bool,
            }}

            pub struct {model_name}Ref<'a> {{
                model: &'a {model_name},
            }}
        "}
    })
}

fn display_symbol_scope_impl<'a>(
    sym_scope: SymbolScope,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    let model_name = display_symbol_scope_name(sym_scope, eqlog, identifiers);
    FmtFn(move |f: &mut Formatter| -> Result {
        let type_fns = iter_symbol_scope_types(sym_scope, eqlog)
            .map(|typ| display_type_symbol_scope_fns(typ, sym_scope, eqlog, identifiers))
            .format("\n");
        let rel_fns = iter_symbol_scope_relations(sym_scope, eqlog)
            .map(|rel| display_relation_symbol_scope_fns(rel, eqlog, identifiers))
            .format("\n");

        let new_fn = display_symbol_scope_new_fn(sym_scope, eqlog, identifiers);
        let canonicalize_fn = display_canonicalize_fn(sym_scope, eqlog, identifiers);
        let drop_dirt_fn = display_drop_dirt_fn(sym_scope, eqlog, identifiers);
        let is_dirty_fn = display_is_dirty_fn(sym_scope, eqlog, identifiers);
        let merge_fn = display_merge_fn(sym_scope, eqlog, identifiers);

        writedoc! {f, "
            impl {model_name} {{
                {new_fn}
                {canonicalize_fn}
                {is_dirty_fn}
                {drop_dirt_fn}
                {type_fns}
                {rel_fns}
                {merge_fn}
            }}
        "}
    })
}

fn display_type_symbol_scope_fns<'a>(
    typ: Type,
    _sym_scope: SymbolScope,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    let type_snake = identifiers
        .get(&eqlog.type_name(typ).unwrap())
        .unwrap()
        .as_str()
        .to_case(Snake);
    let type_camel = type_snake.to_case(UpperCamel);
    FmtFn(move |f: &mut Formatter| -> Result {
        writedoc! {f, "
            /// Returns an iterator over elements of type `{type_camel}`.
            /// The iterator yields canonical representatives only.
            #[allow(dead_code)]
            pub fn iter_{type_snake}(&self) -> impl '_ + Iterator<Item={type_camel}> {{
                self.{type_snake}_new.iter().chain(self.{type_snake}_old.iter()).copied()
            }}

            /// Returns the canonical representative of the equivalence class of `el`.
            #[allow(dead_code)]
            pub fn root_{type_snake}(&self, el: {type_camel}) -> {type_camel} {{
                if el.0 as usize >= self.{type_snake}_equalities.len() {{
                    el
                }} else {{
                    self.{type_snake}_equalities.root_const(el)
                }}
            }}

            /// Returns `true` if `lhs` and `rhs` are in the same equivalence class.
            #[allow(dead_code)]
            pub fn are_equal_{type_snake}(&self, lhs: {type_camel}, rhs: {type_camel}) -> bool {{
                self.root_{type_snake}(lhs) == self.root_{type_snake}(rhs)
            }}

            /// Enforces the equality `lhs = rhs`.
            #[allow(dead_code)]
            pub fn equate_{type_snake}(&mut self, mut lhs: {type_camel}, mut rhs: {type_camel}) {{
                lhs = self.{type_snake}_equalities.root(lhs);
                rhs = self.{type_snake}_equalities.root(rhs);
                if lhs == rhs {{
                    return;
                }}

                let lhs_weight = self.{type_snake}_weights[lhs.0 as usize];
                let rhs_weight = self.{type_snake}_weights[rhs.0 as usize];
                let (root, child) =
                    if lhs_weight >= rhs_weight {{
                        (lhs, rhs)
                    }} else {{
                        (rhs, lhs)
                    }};

                self.{type_snake}_equalities.union_roots_into(child, root);
                
                self.{type_snake}_old.remove(&child);
                self.{type_snake}_new.remove(&child);
                self.{type_snake}_uprooted.push(child);
            }}

            #[allow(dead_code)]
            fn new_{type_snake}_internal(&mut self) -> {type_camel} {{
                let old_len = self.{type_snake}_equalities.len();
                self.{type_snake}_equalities.increase_size_to(old_len + 1);
                let el = {type_camel}::from(u32::try_from(old_len).unwrap());

                self.{type_snake}_new.insert(el);

                assert!(self.{type_snake}_weights.len() == old_len);
                self.{type_snake}_weights.push(0);

                el
            }}
        "}?;
        if eqlog.is_normal_type(typ) {
            writedoc! {f, "
                /// Adjoins a new element of type [{type_camel}].
                #[allow(dead_code)]
                pub fn new_{type_snake}(&mut self) -> {type_camel} {{
                    self.new_{type_snake}_internal()
                }}
            "}?;
        } else if eqlog.is_enum_type(typ) {
            let new_element_fn = display_new_enum_element(typ, eqlog, identifiers);
            let cases_fn = display_enum_cases_fn(typ, eqlog, identifiers);
            writedoc! {f, "
                {new_element_fn}
                {cases_fn}
            "}?;
        } else if eqlog.is_model_type(typ) {
            let new_fn = display_new_model_element(typ, eqlog, identifiers);
            let get_model_fns = display_get_model_fns(typ, eqlog, identifiers);
            writedoc! { f, "
                {new_fn}
                {get_model_fns}
            "}?;
        } else {
            // TODO: Introduce an Eqlog enum, e.g. "TypeKind" so that we can replace this if/else
            // with an exhaustive match.
            panic!("Unexpected type");
        }

        Ok(())
    })
}

fn display_relation_symbol_scope_fns<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let pub_iter_fn = display_pub_iter_fn(rel, eqlog, identifiers);
        let pub_insert_fn = display_pub_insert_relation(rel, eqlog, identifiers);
        writedoc! {f, "
            {pub_iter_fn}
            {pub_insert_fn}
        "}?;
        match eqlog.rel_case(rel) {
            RelCase::PredRel(pred) => {
                writeln!(
                    f,
                    "{}",
                    display_pub_predicate_holds_fn(pred, eqlog, identifiers)
                )?;
            }
            RelCase::FuncRel(func) => {
                writeln!(
                    f,
                    "{}",
                    display_pub_function_eval_fn(func, eqlog, identifiers)
                )?;
                if eqlog.function_can_be_made_defined(func) {
                    writeln!(f, "{}", display_define_fn(func, eqlog, identifiers))?;
                }
            }
        }

        Ok(())
    })
}

fn write_theory_impl(
    out: &mut impl Write,
    name: &str,
    rules: &[FlatRule],
    analyses: &[FlatRuleAnalysis],
    module: ModuleNode,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
) -> io::Result<()> {
    write!(out, "impl {} {{\n", name)?;

    write_close_fn(out)?;
    write_close_until_fn(out, module, rules, eqlog, identifiers)?;

    write!(out, "\n")?;

    assert_eq!(
        rules.len(),
        analyses.len(),
        "There should be precisely one analysis for each rule"
    );
    for (rule, analysis) in rules.iter().zip(analyses) {
        let rule_fn = display_rule_fns(rule, analysis, module, eqlog, identifiers);
        writeln!(out, "{rule_fn}")?;
    }

    write!(out, "}}\n")?;
    Ok(())
}

pub fn write_module(
    out: &mut impl Write,
    eqlog: &Eqlog,
    identifiers: &BTreeMap<Ident, String>,
    rules: &[FlatRule],
    analyses: &[FlatRuleAnalysis],
    index_selection: &IndexSelection,
) -> io::Result<()> {
    write_imports(out)?;
    write!(out, "\n")?;

    for typ in eqlog.iter_type() {
        let type_struct = display_type_struct(typ, eqlog, identifiers);
        let type_impl = display_type_impl(typ, eqlog, identifiers);
        let type_var_struct_and_impl = display_type_var_struct_and_impl(typ, eqlog, identifiers);
        writedoc! {out, "
            {type_struct}
            {type_impl}
            {type_var_struct_and_impl}
        "}?;
    }
    write!(out, "\n")?;

    for (enum_decl, _, _) in eqlog.iter_enum_decl() {
        writeln!(out, "{}", display_enum(enum_decl, eqlog, identifiers))?;
    }

    for (rel, arity) in iter_relation_arities(eqlog, identifiers) {
        write_relation_struct(out, rel, &arity)?;
        let index_selection = index_selection.get(rel).unwrap();
        let indices: BTreeSet<&IndexSpec> = index_selection.values().flatten().collect();
        write_table_struct(out, rel, &arity, &indices)?;
        write_table_impl(out, rel, &arity, &indices, &index_selection)?;
    }
    for (func, arity) in iter_func_arities(eqlog, identifiers) {
        let dom = &arity[0..arity.len() - 1];
        write_func_args_struct(out, func, dom)?;
    }

    write!(out, "\n")?;

    for sym_scope in eqlog.iter_symbol_scope() {
        let model_struct = display_symbol_scope_struct(sym_scope, eqlog, identifiers);
        let model_impl = display_symbol_scope_impl(sym_scope, eqlog, identifiers);

        let delta_struct = display_symbol_scope_delta_struct(sym_scope, eqlog, identifiers);
        let delta_impl = display_symbol_scope_delta_impl(sym_scope, eqlog, identifiers);
        writedoc! {out, "
            {model_struct}
            {model_impl}

            {delta_struct}
            {delta_impl}
        "}?;
    }

    let module = eqlog
        .iter_module_node()
        .next()
        .expect("There should be exactly one module node");
    let module_sym_scope = eqlog.module_symbol_scope(module).unwrap();
    let name: Ident = eqlog.symbol_scope_name(module_sym_scope).unwrap();
    let name: &str = identifiers.get(&name).unwrap().as_str();

    write_theory_impl(out, name, rules, analyses, module, eqlog, identifiers)?;

    Ok(())
}
