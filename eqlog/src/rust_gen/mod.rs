mod rule;
mod types;

pub use rule::*;
pub use types::*;

use crate::eqlog_util::*;
use crate::flat_eqlog::*;
use crate::fmt_util::*;
use crate::ram::*;
use convert_case::{Case, Casing};
use eqlog_eqlog::*;
use indoc::{formatdoc, writedoc};
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{Display, Formatter, Result};
use std::iter::once;

use Case::{Snake, UpperCamel, UpperSnake};

impl From<usize> for ElVar {
    fn from(i: usize) -> Self {
        ElVar {
            name: format!("el{i}").into(),
        }
    }
}

fn display_func_snake<'a>(
    func: Func,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    let ident = eqlog
        .iter_semantic_func()
        .find_map(|(_sym_scope, ident, func0)| eqlog.are_equal_func(func, func0).then_some(ident))
        .expect("should be surjective");
    format!("{}", identifiers.get(&ident).unwrap()).to_case(Snake)
}

fn display_imports() -> impl Display {
    FmtFn(|f| {
        writedoc! { f, "
            #[allow(unused)]
            use std::collections::{{btree_set, BTreeSet, BTreeMap}};
            #[allow(unused)]
            use std::fmt;
            #[allow(unused)]
            use eqlog_runtime::*;
            #[allow(unused)]
            use std::ops::Bound;
            #[allow(unused)]
            use std::ptr::NonNull;
        "}
    })
}

// #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
// pub struct SortName(pub u32);
fn display_sort_struct(sort: &str) -> impl Display + '_ {
    FmtFn(move |f| {
        writedoc! {f, "
            #[allow(dead_code)]
            #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
            pub struct {sort}(pub u32);
        "}
    })
}

fn display_sort_impl(sort: &str) -> impl Display + '_ {
    FmtFn(move |f| {
        writedoc! {f, "
            impl Into<u32> for {sort} {{ fn into(self) -> u32 {{ self.0 }} }}
            impl From<u32> for {sort} {{ fn from(x: u32) -> Self {{ {sort}(x) }} }}
            impl fmt::Display for {sort} {{
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
        let domain: Vec<Type> = type_list_vec(
            eqlog.flat_domain(ctor_func).expect("should be total"),
            eqlog,
        );

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

fn display_func_args_struct<'a>(
    func: Func,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel = eqlog.func_rel(func).unwrap();
        let func_camel = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        let dom = type_list_vec(eqlog.flat_domain(func).unwrap(), eqlog);
        let args = dom
            .iter()
            .copied()
            .map(|typ| {
                FmtFn(move |f| {
                    let type_camel = display_type(typ, eqlog, identifiers)
                        .to_string()
                        .to_case(UpperCamel);
                    write!(f, "pub {type_camel}")
                })
            })
            .format(", ");
        // The #[allow(unused)] is there for functions that cannot be made defined via the Rust API. At
        // the moment, those are non-constructor functions valued in an enum type.
        writedoc! {f, "
            #[allow(unused)]
            #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
            struct {func_camel}Args({args});
        "}
    })
}

fn display_sort_fields(sort: String) -> impl Display {
    FmtFn(move |f| {
        let sort_snake = sort.to_case(Snake);
        writedoc! {f, "
            {sort_snake}_equalities: Unification<{sort}>,
            {sort_snake}_weights: Vec<usize>,
            {sort_snake}_uprooted: Vec<{sort}>,
        "}
    })
}

fn display_is_dirty_fn<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let sets_dirty = eqlog
            .iter_rel()
            .map(FlatInRel::EqlogRel)
            .chain(eqlog.iter_type().map(FlatInRel::TypeSet))
            .map(|rel: FlatInRel| {
                FmtFn(move |f| {
                    let query_spec = QuerySpec::all_new();

                    // See index_selection.rs for why the expectations hold.
                    let index = index_selection
                        .get(&(rel.clone(), query_spec))
                        .expect("should have indices for all new tuples in every type/relation")
                        .as_slice();
                    assert!(
                        index.len() == 1,
                        "Expected exactly one index for dirty tuples"
                    );

                    let field_name = display_index_field_name(&rel, &index[0], eqlog, identifiers);
                    write!(f, "|| !self.{field_name}.is_empty()")
                })
            })
            .format("\n");

        let uprooted_dirty = eqlog
            .iter_type()
            .map(|typ| {
                FmtFn(move |f| {
                    let type_snake = display_type(typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    write!(f, "|| !self.{type_snake}_uprooted.is_empty()")
                })
            })
            .format("\n");

        writedoc! {f, "
            fn is_dirty(&self) -> bool {{
            self.empty_join_is_dirty
            {sets_dirty}
            {uprooted_dirty}
            }}
        "}
    })
}

fn display_pub_predicate_holds_fn<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let relation_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        let arity_types: Vec<Type> = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
        let arity_camel: Vec<String> = arity_types
            .iter()
            .map(|&typ| {
                display_type(typ, eqlog, identifiers)
                    .to_string()
                    .to_case(UpperCamel)
            })
            .collect();

        let rel_fn_args = arity_camel
            .iter()
            .enumerate()
            .format_with("", |(i, s), f| f(&format_args!(", mut arg{i}: {s}")));

        let canonicalize = arity_camel
            .iter()
            .enumerate()
            .format_with("\n", |(i, s), f| {
                let sort_snake = s.to_case(Snake);
                f(&format_args!("arg{i} = self.root_{sort_snake}(arg{i});"))
            });

        let rel_args_doc =
            (0..arity_types.len()).format_with(", ", |i, f| f(&format_args!("arg{i}")));

        let rel = FlatInRel::EqlogRel(rel);
        let query = QuerySpec::one(rel.clone(), eqlog);
        let indices = index_selection
            .get(&(rel.clone(), query))
            .expect("should have indices for relation")
            .as_slice();
        let rel = &rel;

        let checks = indices
            .into_iter()
            .map(|index_spec| {
                let index = display_index_field_name(rel, &index_spec, eqlog, identifiers);
                let IndexSpec { order, age: _ } = index_spec;
                let row_args = order
                    .iter()
                    .map(|i| FmtFn(move |f| write!(f, "arg{i}.0")))
                    .format(", ");
                FmtFn(move |f| write!(f, "|| self.{index}.contains([{row_args}])"))
            })
            .format("\n");

        writedoc! {f, "
            /// Returns `true` if `{relation_snake}({rel_args_doc})` holds.
            #[allow(dead_code)]
            pub fn {relation_snake}(&self{rel_fn_args}) -> bool {{
            {canonicalize}

            false
            {checks}
            }}
        "}
    })
}

fn display_pub_function_eval_fn<'a>(
    func: Func,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    index_selection: &'a IndexSelection,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel = eqlog.func_rel(func).unwrap();

        let relation = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        let relation_snake = relation.to_case(Snake);
        let relation_snake = relation_snake.as_str();

        let flat_dom = type_list_vec(eqlog.flat_domain(func).unwrap(), eqlog);
        let flat_dom_len = flat_dom.len();

        let cod = eqlog.codomain(func).unwrap();
        let cod_camel = display_type(cod, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        let cod_camel = &cod_camel;

        let params = flat_dom
            .iter()
            .copied()
            .enumerate()
            .map(|(i, typ)| {
                FmtFn(move |f| {
                    let type_camel = display_type(typ, eqlog, identifiers)
                        .to_string()
                        .to_case(UpperCamel);
                    write!(f, "mut arg{i}: {type_camel}, ")
                })
            })
            .format("");

        let result_type = FmtFn(move |f| {
            if eqlog.is_total_func(func) {
                write!(f, "{cod_camel}")
            } else {
                write!(f, "Option<{cod_camel}>")
            }
        });

        let canonicalize = flat_dom
            .iter()
            .copied()
            .enumerate()
            .map(|(i, typ)| {
                FmtFn(move |f| {
                    let type_snake = display_type(typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    write!(f, "arg{i} = self.root_{type_snake}(arg{i});")
                })
            })
            .format("\n");

        let doc_args = (0..flat_dom.len())
            .map(|i| FmtFn(move |f| write!(f, "arg{i}")))
            .format(", ")
            .to_string();

        let query_spec = QuerySpec::eval_func(func, eqlog);
        let flat_in_rel = FlatInRel::EqlogRel(rel);

        let indices = index_selection
            .get(&(flat_in_rel.clone(), query_spec))
            .unwrap();

        let flat_in_rel = &flat_in_rel;

        let or_else_get_from = indices
            .into_iter()
            .map(move |index| {
                FmtFn(move |f| {
                    let field = display_index_field_name(&flat_in_rel, &index, eqlog, identifiers);
                    assert_eq!(*index.order.last().unwrap(), flat_dom_len);

                    let gets = index.order[0..index.order.len() - 1]
                        .iter()
                        .map(|i| FmtFn(move |f| write!(f, "let set = set.get(arg{i}.0)?;")))
                        .format("\n");
                    writedoc! {f, "
                        .or_else(move || -> Option<u32> {{
                            let set = &self.{field};
                            {gets}
                            let [result] = set.iter().next()?;
                            Some(result)
                        }})
                    "}
                })
            })
            .format("\n");

        let result = if eqlog.is_total_func(func) {
            "result.unwrap().into()"
        } else {
            "result.map(|x| x.into())"
        };

        writedoc! {f, "
            /// Evaluates `{relation_snake}({doc_args})`.
            #[allow(dead_code)]
            pub fn {relation_snake}(&self, {params}) -> {result_type} {{
            {canonicalize}

            let result: Option<u32> =
            None
            {or_else_get_from}
            ;

            {result}
            }}
        "}
    })
}

fn display_pub_iter_fn<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let is_function = match eqlog.rel_case(rel) {
            RelCase::FuncRel(_) => true,
            RelCase::PredRel(_) => false,
        };
        let relation = display_rel(rel, eqlog, identifiers);
        let rel_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        let rel_snake = rel_snake.as_str();
        let arity_tys: Vec<Type> = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
        let arity_tys = &arity_tys;
        let arity: Vec<String> = arity_tys
            .iter()
            .map(move |ty| {
                display_type(*ty, eqlog, identifiers)
                    .to_string()
                    .to_case(UpperCamel)
            })
            .collect();
        let arity = arity.as_slice();
        let rel_type = if arity.len() == 1 {
            arity[0].clone()
        } else {
            format!("({})", arity.iter().format(", "))
        };

        let docstring = match (is_function, arity.len()) {
            //(false, 0) => todo!("Shouldn't generate an iter_...() function for truth values."),
            (false, 1) => {
                formatdoc! {"
                    /// Returns an iterator over elements satisfying the `{relation}` predicate.
                "}
            }
            (false, n) => {
                assert!(n != 1);
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
                assert!(n > 1);
                formatdoc! {"
                    /// Returns an iterator over tuples in the graph of the `{relation}` function.
                    /// The relation yielded by the iterator need not be functional if the model is not closed.
                "}
            }
        };

        let flat_in_rel = FlatInRel::EqlogRel(rel);
        let query_spec = QuerySpec::all();
        let indices = index_selection
            .get(&(flat_in_rel.clone(), query_spec))
            .expect("should have indices for relation")
            .as_slice();

        let index_its = indices
            .into_iter()
            .enumerate()
            .map(move |(i, index)| {
                let flat_in_rel = flat_in_rel.clone();
                FmtFn(move |f| {
                    let index_field =
                        display_index_field_name(&flat_in_rel, &index, eqlog, identifiers);
                    let row_unpack_args = index
                        .order
                        .iter()
                        .map(|i| FmtFn(move |f| write!(f, "arg{i}")))
                        .format(",");
                    let row_args = arity_tys
                        .iter()
                        .enumerate()
                        .map(|(i, typ)| {
                            FmtFn(move |f| {
                                let type_camel = display_type(*typ, eqlog, identifiers)
                                    .to_string()
                                    .to_case(UpperCamel);
                                write!(f, "{type_camel}::from(arg{i})")
                            })
                        })
                        .format(",");

                    let row = FmtFn(move |f| {
                        if arity_tys.len() == 1 {
                            write!(f, "{row_args}")
                        } else {
                            write!(f, "({row_args})")
                        }
                    });
                    writedoc! {f, "
                        let index_it{i} =
                        self.{index_field}
                        .iter()
                        .map(|[{row_unpack_args}]| {{
                        {row}
                        }});
                    "}
                })
            })
            .format("\n");

        let index_it_chains = (0..indices.len())
            .map(|i| FmtFn(move |f| write!(f, ".chain(index_it{i})")))
            .format("");

        writedoc! {f, "
            {docstring}
            #[allow(dead_code)]
            pub fn iter_{rel_snake}(&self) -> impl '_ + Iterator<Item={rel_type}> {{
            {index_its}

            [].into_iter(){index_it_chains}
            }}
        "}
    })
}

/// Displays a block of code that inserts the variable row into the indices for a Rel.
fn display_insert_row_block<'a>(
    args: &'a [ElVar],
    age: IndexAge,
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    index_selection: &'a IndexSelection,
) -> impl 'a + Display {
    index_set(index_selection)
        .into_iter()
        .filter(move |(flat_in_rel, index)| {
            if index.age != age {
                return false;
            }

            match flat_in_rel {
                FlatInRel::EqlogRel(r0) => *r0 == rel,
                FlatInRel::EqlogRelWithDiagonals {
                    rel: r0,
                    equalities: _,
                } => *r0 == rel,
                FlatInRel::Equality(_) | FlatInRel::TypeSet(_) => false,
            }
        })
        .map(move |(flat_in_rel, index)| {
            FmtFn(move |f| {
                let index_name = display_index_field_name(&flat_in_rel, &index, eqlog, identifiers);
                if let FlatInRel::EqlogRelWithDiagonals { rel: _, equalities } = &flat_in_rel {
                    let checks = equalities
                        .iter()
                        .copied()
                        .enumerate()
                        .filter(|(i, j)| i != j)
                        .map(move |(i, j)| {
                            FmtFn(move |f| {
                                let argi = args[i].clone();
                                let argj = args[j].clone();
                                write!(f, "{argi} == {argj}")
                            })
                        })
                        .format(" || ");
                    let relevant_args: Vec<ElVar> = equalities
                        .iter()
                        .copied()
                        .enumerate()
                        .filter_map(|(i, j)| if i == j { Some(args[i].clone()) } else { None })
                        .collect();
                    let args = index
                        .order
                        .iter()
                        .map(|i| relevant_args[*i].clone())
                        .format(", ");

                    writedoc! {f, "
                        if {checks} {{
                        self.{index_name}.insert([{args}]);
                        }}
                    "}
                } else {
                    let args = index.order.iter().map(|i| args[*i].clone()).format(", ");
                    writedoc! {f, "
                        self.{index_name}.insert([{args}]);
                    "}
                }
            })
        })
        .format("\n")
}

fn display_pub_insert_relation<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    index_selection: &'a IndexSelection,
    is_function: bool,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        let rel_snake = rel_snake.as_str();

        let arity_types = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
        let arity_camel: Vec<String> = arity_types
            .iter()
            .map(|&typ| {
                display_type(typ, eqlog, identifiers)
                    .to_string()
                    .to_case(UpperCamel)
            })
            .collect();

        let rel_args: Vec<ElVar> = (0..arity_types.len()).map(ElVar::from).collect();
        let rel_args = rel_args.as_slice();

        let rel_fn_args = rel_args
            .iter()
            .cloned()
            .zip(arity_camel.iter())
            .map(|(arg, typ_camel)| {
                FmtFn(move |f: &mut Formatter| -> Result { write!(f, "{arg}: {typ_camel}") })
            })
            .format(", ");

        let canonicalize = rel_args
            .iter()
            .cloned()
            .zip(arity_types.iter())
            .map(|(arg, typ)| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let type_snake = display_type(*typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    write!(f, "let {arg}: u32 = self.root_{type_snake}({arg}).0;")
                })
            })
            .format("\n");

        let weight_static_name = display_weight_static_name(rel, eqlog, identifiers).to_string();
        let update_weights = rel_args
            .iter()
            .cloned()
            .zip(arity_types.iter())
            .enumerate()
            .map(move |(i, (arg, typ))| {
                let weight_static_name = weight_static_name.clone();
                FmtFn(move |f: &mut Formatter| -> Result {
                    let type_snake = display_type(*typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    writedoc! {f, "
                        let weight{i}: &mut usize = &mut self.{type_snake}_weights[usize::try_from({arg}).unwrap()];
                        *weight{i} = weight{i}.saturating_add({weight_static_name});
                    "}
                })
            })
            .format("\n");

        let docstring = if is_function {
            let dom_len = arity_types.len() - 1;
            let func_args = rel_args[..dom_len]
                .iter()
                .cloned()
                .map(display_var)
                .format(", ");
            let result = rel_args
                .last()
                .expect("func can't have empty arity")
                .clone();
            formatdoc! {"
                /// Makes the equation `{rel_snake}({func_args}) = {result}` hold.
            "}
        } else {
            let rel_args = rel_args.iter().cloned().map(display_var).format(", ");
            formatdoc! {"
                /// Makes `{rel_snake}({rel_args})` hold.
            "}
        };

        let index_inserts = display_insert_row_block(
            rel_args,
            IndexAge::New,
            rel,
            eqlog,
            identifiers,
            index_selection,
        );

        let flat_rel = FlatInRel::EqlogRel(rel);
        let contains_query = QuerySpec::one(flat_rel.clone(), eqlog);
        let contains_indices = index_selection
            .get(&(flat_rel.clone(), contains_query))
            .expect("should have indices for relation")
            .as_slice();

        let flat_rel = &flat_rel;
        let contains_checks = contains_indices
            .into_iter()
            .map(|index_spec| {
                let index = display_index_field_name(flat_rel, &index_spec, eqlog, identifiers);
                let IndexSpec { order, age: _ } = index_spec;
                let row_args = order.iter().map(|i| rel_args[*i].clone()).format(", ");
                FmtFn(move |f| {
                    writedoc! {f, "
                        if self.{index}.contains([{row_args}]) {{
                        return;
                        }}
                    "}
                })
            })
            .format("\n");

        let mut type_positions: BTreeMap<Type, Vec<usize>> = BTreeMap::new();
        for (i, typ) in arity_types.iter().copied().enumerate() {
            type_positions.entry(typ).or_default().push(i);
        }

        let el_index_inserts = type_positions
            .iter()
            .map(move |(typ, positions)| {
                (0..positions.len())
                    .map(move |pos_index| {
                        FmtFn(move |f| {
                            let pos = positions[pos_index];
                            let pos_arg = rel_args[pos].clone();
                            let checks = (0..pos_index)
                                .map(move |prev_pos_index| {
                                    let prev_pos = positions[prev_pos_index];
                                    let prev_pos_arg = rel_args[prev_pos].clone();
                                    let pos_arg = pos_arg.clone();
                                    FmtFn(move |f| write!(f, "&& {pos_arg} != {prev_pos_arg}"))
                                })
                                .format(" ");

                            let pos_arg = rel_args[pos].clone();
                            let rel_args = rel_args.iter().format(", ");
                            let el_index_field =
                                display_element_index_field_name(rel, *typ, eqlog, identifiers)
                                    .to_string();
                            writedoc! {f, "
                            if true {checks} {{
                            self.{el_index_field}.entry({pos_arg}).or_default().push([{rel_args}]);
                            }}
                        "}
                        })
                    })
                    .format("\n")
            })
            .format("\n");

        writedoc! {f, "
            {docstring}
            #[allow(dead_code)]
            pub fn insert_{rel_snake}(&mut self, {rel_fn_args}) {{
                {canonicalize}

                {contains_checks}

                {index_inserts}

                {el_index_inserts}

                {update_weights}
            }}
        "}
    })
}

fn display_new_element_fn_internal<'a>(
    typ: Type,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let type_camel = display_type(typ, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        let type_snake = type_camel.to_case(Snake);
        let type_snake = type_snake.as_str();

        let parent_func = eqlog.parent_model_func(typ);
        let parent_param = FmtFn(move |f| {
            let parent_func = match parent_func {
                Some(parent_func) => parent_func,
                None => return Ok(()),
            };

            let parent_type = eqlog.codomain(parent_func).unwrap();
            write!(
                f,
                "parent: {}",
                display_type(parent_type, eqlog, identifiers)
            )
        });

        let insert_parent = FmtFn(move |f| {
            if parent_func.is_none() {
                return Ok(());
            }

            write!(f, "self.insert_{type_snake}_parent(el.into(), parent);")
        });

        let new_index = IndexSpec {
            order: vec![0].into(),
            age: IndexAge::New,
        };

        let type_set_rel = FlatInRel::TypeSet(typ);
        let new_index_field =
            display_index_field_name(&type_set_rel, &new_index, eqlog, identifiers);

        writedoc! {f, "
            /// Adjoins a new element of type [{type_camel}].
            #[allow(dead_code)]
            fn new_{type_snake}_internal(&mut self, {parent_param}) -> {type_camel} {{
                let old_len = self.{type_snake}_equalities.len();
                self.{type_snake}_equalities.increase_size_to(old_len + 1);
                let el = u32::try_from(old_len).unwrap();

                self.{new_index_field}.insert([el]);

                assert!(self.{type_snake}_weights.len() == old_len);
                self.{type_snake}_weights.push(0);

                {insert_parent}

                {type_camel}::from(el)
            }}
        "}
    })
}

fn display_new_element_fn<'a>(
    typ: Type,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let type_camel = display_type(typ, eqlog, identifiers)
            .to_string()
            .to_case(UpperCamel);
        let type_snake = type_camel.to_case(Snake);

        let parent_func = eqlog.parent_model_func(typ);
        let parent_param = FmtFn(move |f| {
            let parent_func = match parent_func {
                Some(parent_func) => parent_func,
                None => return Ok(()),
            };

            let parent_type = eqlog.codomain(parent_func).unwrap();
            write!(
                f,
                "parent: {}",
                display_type(parent_type, eqlog, identifiers)
            )
        });

        let parent_arg = FmtFn(move |f| {
            if parent_func.is_none() {
                return Ok(());
            }
            write!(f, "parent")
        });

        writedoc! {f, "
            /// Adjoins a new element of type [{type_camel}].
            #[allow(dead_code)]
            pub fn new_{type_snake}(&mut self, {parent_param}) -> {type_camel} {{
                self.new_{type_snake}_internal({parent_arg})
            }}
        "}
    })
}

fn display_new_enum_element<'a>(
    enum_decl: EnumDeclNode,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f: &mut Formatter| -> Result {
        let enum_ident = eqlog
            .iter_enum_decl()
            .find_map(|(enum_decl0, enum_ident, _)| {
                if enum_decl0 == enum_decl {
                    Some(enum_ident)
                } else {
                    None
                }
            })
            .unwrap();
        let enum_name = identifiers.get(&enum_ident).unwrap();
        let enum_name_camel = enum_name.to_case(UpperCamel);
        let enum_name_camel = enum_name_camel.as_str();
        let enum_name_snake = enum_name.to_case(Snake);

        let ctors = eqlog.iter_ctor_enum().filter_map(|(ctor, enum_decl0)| {
            if eqlog.are_equal_enum_decl_node(enum_decl0, enum_decl) {
                Some(ctor)
            } else {
                None
            }
        });

        let match_branches = ctors
            .map(|ctor| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let ctor_sym_scope = eqlog.ctor_symbol_scope(ctor).unwrap();
                    let ctor_ident = eqlog
                        .iter_ctor_decl()
                        .find_map(|(ctor0, ident, _)| {
                            if eqlog.are_equal_ctor_decl_node(ctor, ctor0) {
                                Some(ident)
                            } else {
                                None
                            }
                        })
                        .unwrap();
                    let ctor_name = identifiers.get(&ctor_ident).unwrap();
                    let ctor_name_snake = ctor_name.to_case(Snake);
                    let ctor_name_camel = ctor_name.to_case(UpperCamel);

                    let ctor_func: Func = eqlog.semantic_func(ctor_sym_scope, ctor_ident).unwrap();
                    let ctor_arg_types: Vec<Type> =
                        type_list_vec(eqlog.flat_domain(ctor_func).unwrap(), eqlog);
                    let ctor_vars = (0..ctor_arg_types.len()).map(ElVar::from).format(", ");
                    let func_vars = ctor_vars.clone();

                    writedoc! {f, "
                        {enum_name_camel}Case::{ctor_name_camel}({ctor_vars}) => {{
                            self.define_{ctor_name_snake}({func_vars})
                        }}
                    "}
                })
            })
            .format("");

        writedoc! {f, "
            /// Adjoins a new element of type [{enum_name_camel}].
            #[allow(dead_code)]
            pub fn new_{enum_name_snake}(&mut self, value: {enum_name_camel}Case) -> {enum_name_camel} {{
                match value {{
                    {match_branches}
                }}
            }}
        "}
    })
}

fn display_enum_cases_fn<'a>(
    enum_decl: EnumDeclNode,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f: &mut Formatter| -> Result {
        let enum_ident = eqlog
            .iter_enum_decl()
            .find_map(|(enum_decl0, enum_ident, _)| {
                if enum_decl0 == enum_decl {
                    Some(enum_ident)
                } else {
                    None
                }
            })
            .unwrap();
        let enum_name = identifiers.get(&enum_ident).unwrap();
        let enum_name_camel = enum_name.to_case(UpperCamel);
        let enum_name_camel = enum_name_camel.as_str();
        let enum_name_snake = enum_name.to_case(Snake);

        let ctors = eqlog.iter_ctor_enum().filter_map(|(ctor, enum_decl0)| {
            if eqlog.are_equal_enum_decl_node(enum_decl0, enum_decl) {
                Some(ctor)
            } else {
                None
            }
        });

        let ctor_value_iters = ctors
            .map(|ctor| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let ctor_sym_scope = eqlog.ctor_symbol_scope(ctor).unwrap();
                    let ctor_ident = eqlog
                        .iter_ctor_decl()
                        .find_map(|(ctor0, ident, _)| {
                            if eqlog.are_equal_ctor_decl_node(ctor, ctor0) {
                                Some(ident)
                            } else {
                                None
                            }
                        })
                        .unwrap();
                    let ctor_name = identifiers.get(&ctor_ident).unwrap();
                    let ctor_name_snake = ctor_name.to_case(Snake);
                    let ctor_name_camel = ctor_name.to_case(UpperCamel);

                    let ctor_func: Func = eqlog.semantic_func(ctor_sym_scope, ctor_ident).unwrap();
                    let arg_num = type_list_vec(eqlog.flat_domain(ctor_func).unwrap(), eqlog).len();

                    let ctor_arg_vars = (0..arg_num).map(ElVar::from);
                    let result_var = ElVar::from(arg_num);
                    let tuple_vars = ctor_arg_vars.clone().chain(once(result_var.clone()));

                    let ctor_arg_vars = ctor_arg_vars.format(", ");
                    let tuple_vars = tuple_vars.map(display_var).format(", ");

                    // TODO: We probably want to use an index insted of a linear search here.
                    // However, this function is not needed during the close method, so those
                    // indices should only exist when the host program uses this function, probably
                    // lazily. But we don't have machinery for index lifetimes yet.
                    writedoc! {f, "
                        .chain(self.iter_{ctor_name_snake}().filter_map(move |({tuple_vars})| {{
                            if el == {result_var} {{
                                Some({enum_name_camel}Case::{ctor_name_camel}({ctor_arg_vars}))
                            }} else {{
                                None
                            }}
                        }}))
                    "}
                })
            })
            .format("\n");

        // We need to allow the unused parens here in case of nullary constructors. For those, the
        // iter_{ctor_name_snake} function yields elements instead of tuples, but the argument to
        // the closure we pass to filter_map above still has parens around the single variable.
        writedoc! {f, "
            /// Returns an iterator over ways to destructure an [{enum_name_camel}] element.
            #[allow(dead_code)]
            pub fn {enum_name_snake}_cases<'a>(&'a self, el: {enum_name_camel}) -> impl 'a + Iterator<Item = {enum_name_camel}Case> {{
            let el = self.{enum_name_snake}_equalities.root_const(el);
            #[allow(unused_parens)]
            [].into_iter(){ctor_value_iters}
            }}

            /// Returns the first way to destructure an [{enum_name_camel}] element.
            #[allow(dead_code)]
            pub fn {enum_name_snake}_case(&self, el: {enum_name_camel}) -> {enum_name_camel}Case {{
                self.{enum_name_snake}_cases(el).next().unwrap()
            }}
        "}
    })
}

fn display_equate_elements<'a>(
    typ: Type,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let type_camel = format!("{}", display_type(typ, eqlog, identifiers)).to_case(UpperCamel);
        let type_snake = type_camel.to_case(Snake);

        let type_set_rel = FlatInRel::TypeSet(typ);
        let index_new = IndexSpec {
            order: vec![0].into(),
            age: IndexAge::New,
        };
        let index_old = IndexSpec {
            order: vec![0].into(),
            age: IndexAge::Old,
        };

        let index_new = display_index_field_name(&type_set_rel, &index_new, eqlog, identifiers);
        let index_old = display_index_field_name(&type_set_rel, &index_old, eqlog, identifiers);

        writedoc! {f, "
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

                self.{index_new}.remove([child.0]);
                self.{index_old}.remove([child.0]);
                self.{type_snake}_uprooted.push(child);
            }}
        "}
    })
}

fn display_root_fn(sort: &str) -> impl Display + '_ {
    FmtFn(move |f| {
        let sort_snake = sort.to_case(Snake);
        writedoc! {f, "
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
    })
}

fn display_are_equal_fn(sort: &str) -> impl Display + '_ {
    FmtFn(move |f| {
        let sort_snake = sort.to_case(Snake);
        writedoc! {f, "
            /// Returns `true` if `lhs` and `rhs` are in the same equivalence class.
            #[allow(dead_code)]
            pub fn are_equal_{sort_snake}(&self, lhs: {sort}, rhs: {sort}) -> bool {{
                self.root_{sort_snake}(lhs) == self.root_{sort_snake}(rhs)
            }}
        "}
    })
}

fn display_iter_type_fn<'a>(
    typ: Type,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    index_selection: &'a IndexSelection,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let type_snake = display_type(typ, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        let type_camel = type_snake.to_case(UpperCamel);
        let rel = FlatInRel::TypeSet(typ);
        let query = QuerySpec::all();
        let indices = index_selection.get(&(rel.clone(), query)).unwrap();

        let index_chain_iter = indices
            .into_iter()
            .map(move |index| {
                assert_eq!(index.order.len(), 1);

                let rel = rel.clone();
                FmtFn(move |f| {
                    let index_field = display_index_field_name(&rel, index, eqlog, identifiers);
                    writedoc! {f, "
                        .chain(self.{index_field}.iter())
                    "}
                })
            })
            .format("\n");

        writedoc! {f, "
            /// Returns and iterator over elements of type `{type_camel}`.
            /// The iterator yields canonical representatives only.
            #[allow(dead_code)]
            pub fn iter_{type_snake}(&self) -> impl '_ + Iterator<Item={type_camel}> {{
            [].into_iter()
            {index_chain_iter}
            .map(|[el]| {type_camel}::from(el))
            }}
        "}
    })
}

fn display_remove_from_index_expr<'a>(
    rel: FlatInRel,
    index: IndexSpec,
    row_args: &'a [ElVar],
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let equalities = match &rel {
            FlatInRel::EqlogRel(_) => None,
            FlatInRel::EqlogRelWithDiagonals { rel: _, equalities } => Some(equalities),
            FlatInRel::Equality(_) | FlatInRel::TypeSet(_) => None,
        };

        let row_args: Vec<ElVar> = match equalities {
            Some(equalities) => row_args
                .iter()
                .cloned()
                .enumerate()
                .filter_map(|(i, row_arg)| {
                    if equalities[i] == i {
                        Some(row_arg)
                    } else {
                        None
                    }
                })
                .collect(),
            None => row_args.to_vec(),
        };

        let permuted_row_args = index
            .order
            .iter()
            .map(|i| row_args[*i].clone())
            .format(", ");

        let field_name = display_index_field_name(&rel, &index, eqlog, identifiers);

        write!(f, "self.{field_name}.remove([{permuted_row_args}])")
    })
}

fn display_canonicalize_rel_block<'a>(
    rel: Rel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    index_selection: &'a IndexSelection,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);

        let arity = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
        let arity_len = arity.len();
        let types: BTreeSet<_> = arity.iter().copied().collect();
        let row_args: Vec<ElVar> = (0..arity.len()).map(ElVar::from).collect();
        let row_args = row_args.as_slice();

        let fill_non_canonical_rows_vec = types
            .into_iter()
            .map(|typ| {
                FmtFn(move |f| {
                    let type_snake = display_type(typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    let element_index_field =
                        display_element_index_field_name(rel, typ, eqlog, identifiers);

                    writedoc! {f, "
                        for el in self.{type_snake}_uprooted.iter().copied() {{
                        if let Some(rows) = self.{element_index_field}.remove(&el.0) {{
                        non_canonical_rows.push(rows);
                        }}
                        }}
                    "}
                })
            })
            .format("\n");

        let reduce_weights =
            arity
                .iter()
                .copied()
                .enumerate()
                .map(move |(i, type_i)| {
                    FmtFn(move |f| {
                        let type_i_snake = display_type(type_i, eqlog, identifiers)
                            .to_string()
                            .to_case(Snake);
                        let weight_static_name =
                            display_weight_static_name(rel, eqlog, identifiers);
                        let el = row_args[i].clone();
                        writedoc! {f, "
                            let weight{i}: &mut usize = &mut self.{type_i_snake}_weights[usize::try_from({el}).unwrap()];
                            *weight{i} = weight{i}.saturating_sub({weight_static_name});
                        "}
                    })
                })
                .format("\n");

        let primary_new_indices = index_selection
            .get(&(FlatInRel::EqlogRel(rel), QuerySpec::all_new()))
            .unwrap();
        assert_eq!(primary_new_indices.len(), 1);
        let primary_new_index: IndexSpec = primary_new_indices[0].clone();

        let primary_old_indices = index_selection
            .get(&(FlatInRel::EqlogRel(rel), QuerySpec::all_old()))
            .unwrap();
        assert_eq!(primary_old_indices.len(), 1);
        let primary_old_index: IndexSpec = primary_old_indices[0].clone();

        let mut secondary_new_indices: BTreeSet<(FlatInRel, IndexSpec)> = BTreeSet::new();
        let mut secondary_old_indices: BTreeSet<(FlatInRel, IndexSpec)> = BTreeSet::new();
        for ((r0, _query_spec), indices) in index_selection {
            match r0 {
                FlatInRel::EqlogRel(rel0) => {
                    if *rel0 != rel {
                        continue;
                    }
                }
                FlatInRel::EqlogRelWithDiagonals {
                    rel: rel0,
                    equalities: _,
                } => {
                    if *rel0 != rel {
                        continue;
                    }
                }
                FlatInRel::TypeSet(_) | FlatInRel::Equality(_) => continue,
            };

            for index in indices {
                if r0 == &FlatInRel::EqlogRel(rel) {
                    if *index == primary_new_index || *index == primary_old_index {
                        continue;
                    }
                }

                match index.age {
                    IndexAge::New => {
                        secondary_new_indices.insert((r0.clone(), index.clone()));
                    }
                    IndexAge::Old => {
                        secondary_old_indices.insert((r0.clone(), index.clone()));
                    }
                }
            }
        }

        let remove_from_secondary_new_indices = secondary_new_indices
            .into_iter()
            .map(move |(r, index)| {
                FmtFn(move |f| {
                    let remove_from_index_expr = display_remove_from_index_expr(
                        r.clone(),
                        index.clone(),
                        row_args,
                        eqlog,
                        identifiers,
                    );
                    write!(f, "{remove_from_index_expr};")
                })
            })
            .format("\n");
        let remove_from_secondary_old_indices = secondary_old_indices
            .into_iter()
            .map(move |(r, index)| {
                FmtFn(move |f| {
                    let remove_from_index_expr = display_remove_from_index_expr(
                        r.clone(),
                        index.clone(),
                        row_args,
                        eqlog,
                        identifiers,
                    );
                    write!(f, "{remove_from_index_expr};")
                })
            })
            .format("\n");

        let remove_from_primary_new_index = display_remove_from_index_expr(
            FlatInRel::EqlogRel(rel),
            primary_new_index,
            row_args,
            eqlog,
            identifiers,
        );
        let remove_from_primary_old_index = display_remove_from_index_expr(
            FlatInRel::EqlogRel(rel),
            primary_old_index,
            row_args,
            eqlog,
            identifiers,
        );

        let insert_row_args = row_args
            .iter()
            .zip(arity.iter())
            .map(|(arg, typ)| {
                FmtFn(move |f| {
                    let type_snake = display_type(*typ, eqlog, identifiers)
                        .to_string()
                        .to_case(UpperCamel);
                    write!(f, "{type_snake}({arg})")
                })
            })
            .format(",");

        let row_args = row_args.iter().format(", ");

        writedoc! {f, "
            #[allow(unused_mut)]
            let mut non_canonical_rows: Vec<Vec<[u32; {arity_len}]>> = Vec::new();
            {fill_non_canonical_rows_vec}

            for [{row_args}] in non_canonical_rows.into_iter().flatten() {{
            let was_in_indices = if {remove_from_primary_new_index} {{
            {remove_from_secondary_new_indices}
            true
            }} else if {remove_from_primary_old_index} {{
            {remove_from_secondary_old_indices}
            true
            }} else {{
            false
            }};

            if !was_in_indices {{
            continue;
            }}

            {reduce_weights}

            self.insert_{rel_snake}({insert_row_args});
            }}
        "}
    })
}

fn display_canonicalize_fn<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    index_selection: &'a IndexSelection,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_blocks = eqlog
            .iter_rel()
            .map(|rel| display_canonicalize_rel_block(rel, eqlog, identifiers, index_selection))
            .format("\n");

        let clear_uprooted_vecs = eqlog
            .iter_type()
            .map(|typ| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let type_snake =
                        format!("{}", display_type(typ, eqlog, identifiers)).to_case(Snake);
                    write!(f, "self.{type_snake}_uprooted.clear();")
                })
            })
            .format("\n");

        writedoc! {f, "
            fn canonicalize(&mut self) {{
                {rel_blocks}

                {clear_uprooted_vecs}
            }}
        "}
    })
}

fn display_rel_row_type<'a>(rel: Rel, eqlog: &'a Eqlog) -> impl 'a + Display {
    FmtFn(move |f| {
        let arity_len = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog).len();
        write!(f, "[u32; {arity_len}]")
    })
}

/// Displays the tuple type of the arguments of a function.
fn display_func_args_type<'a>(func: Func, eqlog: &'a Eqlog) -> impl 'a + Display {
    FmtFn(move |f| {
        let dom_list = eqlog.flat_domain(func).unwrap();
        let arity_len = type_list_vec(dom_list, eqlog).len();
        write!(f, "[u32; {arity_len}]")
    })
}

fn display_out_set_field_name<'a>(
    rel: &'a FlatOutRel,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| match rel {
        FlatOutRel::EqlogRel(rel) => {
            let rel_snake = display_rel(*rel, eqlog, identifiers)
                .to_string()
                .to_case(Snake);
            write!(f, "new_{rel_snake}")
        }
        FlatOutRel::Equality(typ) => {
            let type_snake = display_type(*typ, eqlog, identifiers)
                .to_string()
                .to_case(Snake);
            write!(f, "new_{type_snake}_equalities")
        }
        FlatOutRel::FuncDomain(func) => {
            let rel = eqlog.func_rel(*func).unwrap();
            let rel_snake = display_rel(rel, eqlog, identifiers)
                .to_string()
                .to_case(Snake);
            write!(f, "new_{rel_snake}_def")
        }
    })
}

fn display_out_set_type<'a>(rel: &'a FlatOutRel, eqlog: &'a Eqlog) -> impl 'a + Display {
    FmtFn(move |f| {
        let arity_len = rel.arity(eqlog).len();
        write!(f, "Vec<[u32; {arity_len}]>")
    })
}

fn display_model_delta_struct<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let new_tuples = eqlog
            .iter_rel()
            .map(|rel| {
                FmtFn(move |f| {
                    let rel_snake = display_rel(rel, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    let row_type = display_rel_row_type(rel, eqlog);
                    write!(f, "new_{rel_snake}: Vec<{row_type}>,")
                })
            })
            .format("\n");

        let new_equalities = eqlog
            .iter_type()
            .map(|typ| {
                FmtFn(move |f| {
                    let type_snake = display_type(typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    write!(f, "new_{type_snake}_equalities: Vec<[u32; 2]>,")
                })
            })
            .format("\n");

        let new_defines = eqlog
            .iter_func()
            .filter(|func| eqlog.function_can_be_made_defined(*func))
            .map(|func| {
                FmtFn(move |f| {
                    let rel = eqlog.func_rel(func).unwrap();
                    let rel_snake = display_rel(rel, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    let args_type = display_func_args_type(func, eqlog);
                    write!(f, "new_{rel_snake}_def: Vec<{args_type}>,")
                })
            })
            .format("\n");

        writedoc! {f, "
            #[derive(Debug, Clone)]
            struct ModelDelta {{
            {new_tuples}
            {new_equalities}
            {new_defines}
            }}
        "}
    })
}

fn display_model_delta_impl<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        writedoc! {f, "
            impl ModelDelta {{
        "}
        .unwrap();

        let new_fn = display_model_delta_new_fn(eqlog, identifiers);
        write!(f, "{}", new_fn).unwrap();

        let apply_surjective_fn = display_model_delta_apply_surjective_fn();
        write!(f, "{}", apply_surjective_fn).unwrap();

        let apply_non_surjective_fn = display_model_delta_apply_non_surjective_fn();
        write!(f, "{}", apply_non_surjective_fn).unwrap();

        let apply_equalities_fn = display_model_delta_apply_equalities_fn(eqlog, identifiers);
        write!(f, "{}", apply_equalities_fn).unwrap();

        let apply_tuples_fn = display_model_delta_apply_tuples_fn(eqlog, identifiers);
        write!(f, "{}", apply_tuples_fn).unwrap();

        let apply_def_fn = display_model_delta_apply_def_fn(eqlog, identifiers);
        write!(f, "{}", apply_def_fn).unwrap();

        writedoc! {f, "
            }}
        "}
    })
}

fn display_model_delta_new_fn<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let new_tuples = eqlog
            .iter_rel()
            .map(|rel| {
                FmtFn(move |f| {
                    let relation_snake = display_rel(rel, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    write!(f, "new_{relation_snake}: Vec::new(),")
                })
            })
            .format("\n");

        let new_equalities = eqlog
            .iter_type()
            .map(|typ| {
                FmtFn(move |f| {
                    let type_snake = display_type(typ, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    write!(f, "new_{type_snake}_equalities: Vec::new(),")
                })
            })
            .format("\n");
        let new_defines = eqlog
            .iter_func()
            .filter(|&func| eqlog.function_can_be_made_defined(func))
            .map(|func| {
                FmtFn(move |f| {
                    let rel = eqlog.func_rel(func).unwrap();
                    let func_snake = display_rel(rel, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    write!(f, "new_{func_snake}_def: Vec::new(),")
                })
            })
            .format("\n");

        writedoc! {f, "
            fn new() -> ModelDelta {{
                ModelDelta{{
            {new_tuples}
            {new_equalities}
            {new_defines}
                }}
            }}
        "}
    })
}

fn display_model_delta_apply_surjective_fn() -> impl Display {
    FmtFn(|f| {
        writedoc! {f, "
            fn apply_surjective(&mut self, model: &mut Model) {{
                self.apply_equalities(model);
                self.apply_tuples(model);
            }}
        "}
    })
}

fn display_model_delta_apply_non_surjective_fn() -> impl Display {
    FmtFn(|f| {
        writedoc! {f, "
            fn apply_non_surjective(&mut self, model: &mut Model) {{
                self.apply_func_defs(model);
            }}
        "}
    })
}

fn display_model_delta_apply_equalities_fn<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let type_equalities = eqlog
            .iter_type()
            .map(|typ| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let type_snake =
                        format!("{}", display_type(typ, eqlog, identifiers)).to_case(Snake);

                    writedoc! {f, "
                        for [lhs, rhs] in self.new_{type_snake}_equalities.drain(..) {{
                            model.equate_{type_snake}(lhs.into(), rhs.into());
                        }}
                    "}
                })
            })
            .format("\n");

        writedoc! {f, "
            #[allow(unused)]
            fn apply_equalities(&mut self, model: &mut Model) {{
            {type_equalities}
            }}
        "}
    })
}

fn display_model_delta_apply_tuples_fn<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let relations = eqlog
            .iter_rel()
            .map(|rel| {
                FmtFn(move |f| {
                    let arity = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
                    let rel_snake = display_rel(rel, eqlog, identifiers)
                        .to_string()
                        .to_case(Snake);
                    let args_destructure = (0..arity.len())
                        .map(ElVar::from)
                        .map(display_var)
                        .format(", ");
                    let insert_args = (0..arity.len())
                        .map(|i| {
                            FmtFn(move |f| {
                                let var = ElVar::from(i);
                                write!(f, "{var}.into()")
                            })
                        })
                        .format(", ");

                    writedoc! {f, "
                    for [{args_destructure}] in self.new_{rel_snake}.drain(..) {{
                        model.insert_{rel_snake}({insert_args});
                    }}
                "}
                })
            })
            .format("\n");

        // allow(unused_variables) is there for theories without relations.
        writedoc! {f, "
            #[allow(unused_variables)]
            fn apply_tuples(&mut self, model: &mut Model) {{
                {relations}
            }}
        "}
    })
}

fn display_model_delta_apply_def_fn<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let func_defs = eqlog
            .iter_semantic_func()
            .filter_map(|(_, ident, func)| {
                if !eqlog.function_can_be_made_defined(func) {
                    return None;
                }

                let func_name = identifiers.get(&ident).unwrap();
                let func_snake = func_name.to_case(Snake);

                let domain = type_list_vec(eqlog.flat_domain(func).unwrap(), eqlog);

                let args_destructure = (0..domain.len())
                    .map(ElVar::from)
                    .map(display_var)
                    .format(", ");
                let define_args = (0..domain.len())
                    .map(|i| {
                        FmtFn(move |f| {
                            let var = ElVar::from(i);
                            write!(f, "{var}.into()")
                        })
                    })
                    .format(", ");

                Some(FmtFn(move |f: &mut Formatter| -> Result {
                    writedoc! {f, "
                            for [{args_destructure}] in self.new_{func_snake}_def.drain(..) {{
                                model.define_{func_snake}({define_args});
                            }}
                        "}
                }))
            })
            .format("\n");

        // allow(unused_variables) is there for theories without functions.
        writedoc! {f, "
            #[allow(unused_variables)]
            fn apply_func_defs(&mut self, model: &mut Model) {{
                {func_defs}
            }}
        "}
    })
}

impl Display for ElVar {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let ElVar { name } = self;
        write!(f, "{}", name)
    }
}

// TODO: Remove this legacy function.
fn display_var(var: ElVar) -> impl Display {
    var
}

fn display_move_new_to_old_fn<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let relations = eqlog
            .iter_rel()
            .map(|rel| {
                FmtFn(move |f| {
                    let flat_rel = FlatInRel::EqlogRel(rel);
                    let query_new = QuerySpec::all_new();
                    let indices_new = index_selection
                        .get(&(flat_rel.clone(), query_new))
                        .expect("should have indices for all new relations");
                    assert!(
                        indices_new.len() == 1,
                        "should have just one index for all new tuples"
                    );
                    let primary_index_new = &indices_new[0];

                    let args: Vec<ElVar> =
                        (0..flat_rel.arity(eqlog).len()).map(ElVar::from).collect();
                    let primary_new_args = primary_index_new
                        .order
                        .iter()
                        .map(|i| args[*i].clone())
                        .format(", ");

                    let primary_new_index =
                        display_index_field_name(&flat_rel, &primary_index_new, eqlog, identifiers);

                    let old_inserts = display_insert_row_block(
                        args.as_slice(),
                        IndexAge::Old,
                        rel,
                        eqlog,
                        identifiers,
                        index_selection,
                    );

                    let new_clears = index_set(index_selection)
                        .into_iter()
                        .filter(|(flat_in_rel, index)| {
                            match index.age {
                                IndexAge::Old => {
                                    return false;
                                }
                                IndexAge::New => {}
                            }

                            match flat_in_rel {
                                FlatInRel::EqlogRel(rel0) => *rel0 == rel,
                                FlatInRel::EqlogRelWithDiagonals { rel: rel0, .. } => *rel0 == rel,
                                FlatInRel::TypeSet(_) => false,
                                FlatInRel::Equality(_) => false,
                            }
                        })
                        .map(move |(flat_in_rel, index)| {
                            FmtFn(move |f| {
                                let field_name = display_index_field_name(
                                    &flat_in_rel,
                                    &index,
                                    eqlog,
                                    identifiers,
                                );
                                write!(f, "self.{field_name}.clear();")
                            })
                        })
                        .format("\n");

                    writedoc! {f, "
                        for [{primary_new_args}] in self.{primary_new_index}.iter() {{
                        {old_inserts}
                        }}
                        {new_clears}
                    "}
                })
            })
            .format("\n");

        let types = eqlog
            .iter_type()
            .map(|typ| {
                FmtFn(move |f| {
                    let flat_rel = FlatInRel::TypeSet(typ);

                    let index_new = IndexSpec {
                        age: IndexAge::New,
                        order: vec![0].into(),
                    };
                    let index_old = IndexSpec {
                        age: IndexAge::Old,
                        order: index_new.order.clone(),
                    };

                    let new_index =
                        display_index_field_name(&flat_rel, &index_new, eqlog, identifiers);
                    let old_index =
                        display_index_field_name(&flat_rel, &index_old, eqlog, identifiers);

                    writedoc! {f, "
                        for r in self.{new_index}.iter() {{
                        self.{old_index}.insert(r);
                        }}
                        self.{new_index}.clear();
                    "}
                })
            })
            .format("\n");

        writedoc! {f, "
            fn move_new_to_old(&mut self) {{
            self.empty_join_is_dirty = false;

            {relations}

            {types}
            }}
        "}
    })
}

fn display_module_env_var<'a>(
    ram_module: &'a RamModule,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let env_struct_name = display_module_env_struct_name(ram_module);
        let in_set_fields = module_env_in_rels(ram_module)
            .into_iter()
            .map(|(flat_in_rel, index)| {
                FmtFn(move |f| {
                    let field_name =
                        display_index_field_name(&flat_in_rel, &index, eqlog, identifiers);
                    write!(f, "{field_name}: &self.{field_name},")
                })
            })
            .format("\n");

        let out_set_fields = module_env_out_rels(ram_module)
            .into_iter()
            .map(|flat_out_rel| {
                FmtFn(move |f| {
                    let field_name = display_out_set_field_name(&flat_out_rel, eqlog, identifiers);
                    write!(f, "{field_name}: &mut delta.{field_name},")
                })
            })
            .format("\n");

        writedoc! {f, "
            let env = {env_struct_name} {{
                phantom: std::marker::PhantomData,
                {in_set_fields}
                {out_set_fields}
            }};
        "}
    })
}

fn display_close_until_fn<'a>(
    ram_modules: &'a [RamModule],
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let module_calls = ram_modules
            .iter()
            .map(|ram_module| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let name = ram_module.name.as_str();
                    let env_var = display_module_env_var(ram_module, eqlog, identifiers);
                    writedoc! {f, r#"
                        {env_var}
                        {name}(env);
                    "#}
                })
            })
            .format("\n");

        writedoc! {f, "
            /// Closes the model under all axioms until `condition` is satisfied.
            /// Depending on the axioms and `condition`, this may run indefinitely.
            /// Returns `true` if the `condition` eventually holds.
            /// Returns `false` if the model could be closed under all axioms but `condition` still does not hold.
            #[allow(dead_code)]
            pub fn close_until(&mut self, condition: impl Fn(&Self) -> bool) -> bool
            {{
                let mut delta = ModelDelta::new();

                self.canonicalize();
                if condition(self) {{
                    return true;
                }}

                while self.is_dirty() {{
                    loop {{
            {module_calls}

                        self.move_new_to_old();
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
    })
}

fn display_close_fn() -> impl Display {
    FmtFn(|f| {
        writedoc! {f, "
            /// Closes the model under all axioms.
            /// Depending on the axioms and the model, this may run indefinitely.
            #[allow(dead_code)]
            pub fn close(&mut self) {{
                self.close_until(|_: &Self| false);
            }}
        "}
    })
}

fn display_new_fn<'a>(
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        writeln!(f, "/// Creates an empty model.").unwrap();
        writeln!(f, "#[allow(dead_code)]").unwrap();
        writeln!(f, "pub fn new() -> Self {{").unwrap();
        writeln!(f, "Self {{").unwrap();
        for typ in eqlog.iter_type() {
            let type_snake = display_type(typ, eqlog, identifiers)
                .to_string()
                .to_case(Snake);
            writeln!(f, "{type_snake}_equalities: Unification::new(),").unwrap();
            writeln!(f, "{type_snake}_weights: Vec::new(),").unwrap();
            writeln!(f, "{type_snake}_uprooted: Vec::new(),").unwrap();
        }
        for (flat_rel, index) in index_set(index_selection) {
            let field_name = display_index_field_name(&flat_rel, &index, eqlog, identifiers);
            let index_type = display_index_type(&flat_rel, eqlog);
            writeln!(f, "{field_name}: {index_type}::new(),").unwrap();
        }
        for rel in eqlog.iter_rel() {
            let type_set: BTreeSet<Type> = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog)
                .into_iter()
                .collect();
            for typ in type_set {
                let field_name = display_element_index_field_name(rel, typ, eqlog, identifiers);
                writeln!(f, "{field_name}: BTreeMap::new(),").unwrap();
            }
        }
        writeln!(f, "empty_join_is_dirty: true,").unwrap();
        writeln!(f, "}}").unwrap();
        write!(f, "}}").unwrap();
        Ok(())
    })
}

fn display_define_fn<'a>(
    func: Func,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let func_snake = display_func_snake(func, eqlog, identifiers);

        let domain = type_list_vec(eqlog.flat_domain(func).expect("should be total"), eqlog);
        let codomain = eqlog.codomain(func).expect("should be total");

        let codomain_camel =
            format!("{}", display_type(codomain, eqlog, identifiers)).to_case(UpperCamel);
        let codomain_snake = codomain_camel.to_case(Snake);

        let func_arg_vars: Vec<ElVar> = (0..domain.len()).map(ElVar::from).collect();
        let result_var = ElVar::from(domain.len());

        let fn_args = func_arg_vars
            .iter()
            .cloned()
            .zip(domain.iter().copied())
            .map(|(var, var_typ)| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let type_camel = format!("{}", display_type(var_typ, eqlog, identifiers))
                        .to_case(UpperCamel);
                    write!(f, "{var}: {type_camel}")
                })
            })
            .format(", ");

        let args = func_arg_vars
            .iter()
            .cloned()
            .map(display_var)
            .format(", ")
            .to_string();
        let rel_args = func_arg_vars
            .iter()
            .cloned()
            .chain(once(result_var.clone()))
            .map(display_var)
            .format(", ");

        let codomain_parent_func = eqlog.parent_model_func(codomain);
        let parent_arg = FmtFn(move |f| {
            if codomain_parent_func.is_none() {
                return Ok(());
            }

            let parent_var = ElVar::from(0);
            write!(f, "{parent_var}")
        });

        writedoc! {f, "
            /// Enforces that `{func_snake}({args})` is defined, adjoining a new element if necessary.
            #[allow(dead_code)]
            pub fn define_{func_snake}(&mut self, {fn_args}) -> {codomain_camel} {{
                match self.{func_snake}({args}) {{
                    Some(result) => result,
                    None => {{
                        // TODO: The parent var, if any, is only correct if the codomain type
                        // is defined in the same model (and not a parent model) that the function
                        // is declared in.
                        let {result_var} = self.new_{codomain_snake}_internal({parent_arg});
                        self.insert_{func_snake}({rel_args});
                        {result_var}
                    }}
                }}
            }}
        "}
    })
}

impl Display for IndexAge {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            IndexAge::New => write!(f, "new"),
            IndexAge::Old => write!(f, "old"),
        }
    }
}

fn display_index_field_name<'a>(
    rel: &'a FlatInRel,
    index: &'a IndexSpec,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let order = index.order.iter().format("_");
        let age = index.age;
        match rel {
            FlatInRel::EqlogRel(rel) => {
                let rel_snake = display_rel(*rel, eqlog, identifiers)
                    .to_string()
                    .to_case(Snake);
                write!(f, "{rel_snake}_{age}_order_{order}")
            }
            FlatInRel::EqlogRelWithDiagonals { rel, equalities } => {
                let rel_snake = display_rel(*rel, eqlog, identifiers)
                    .to_string()
                    .to_case(Snake);
                let equalities = equalities.iter().format("_");
                write!(f, "{rel_snake}_{age}_eqs_{equalities}_order_{order}")
            }
            FlatInRel::TypeSet(typ) => {
                let type_snake = display_type(*typ, eqlog, identifiers)
                    .to_string()
                    .to_case(Snake);
                write!(f, "{type_snake}_{age}_order_0")
            }
            FlatInRel::Equality(_) => {
                panic!("Equality in relations should have been transformed the equality pass on flat eqlog")
            }
        }
    })
}

fn display_element_index_field_name<'a>(
    rel: Rel,
    typ: Type,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        let type_snake = display_type(typ, eqlog, identifiers)
            .to_string()
            .to_case(Snake);
        write!(f, "{rel_snake}_{type_snake}_element_index")
    })
}

fn display_index_type<'a>(rel: &'a FlatInRel, eqlog: &'a Eqlog) -> impl Display + 'a {
    FmtFn(move |f| {
        let arity_len = rel.arity(eqlog).len();
        write!(f, "PrefixTree{arity_len}")
    })
}

fn display_weight_static_name<'a>(
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

fn display_weight_static<'a>(
    rel: Rel,
    index_selection: &'a IndexSelection,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let static_name = display_weight_static_name(rel, eqlog, identifiers);

        let el_lookup_weight = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog).len();

        let relevant_indices: BTreeSet<(FlatInRel, IndexSpec)> = index_selection
            .iter()
            .filter_map(|((flat_in_rel, _query_spec), index_specs)| {
                match flat_in_rel {
                    FlatInRel::EqlogRel(rel0) => {
                        if *rel0 != rel {
                            return None;
                        }
                    }
                    FlatInRel::EqlogRelWithDiagonals {
                        rel: rel0,
                        equalities: _,
                    } => {
                        if *rel0 != rel {
                            return None;
                        }
                    }
                    FlatInRel::Equality(_) | FlatInRel::TypeSet(_) => {
                        return None;
                    }
                }

                Some((flat_in_rel, index_specs))
            })
            .flat_map(|(flat_in_rel, index_specs)| {
                index_specs.iter().filter_map(|index_spec| {
                    match index_spec.age {
                        IndexAge::New => {
                            return None;
                        }
                        IndexAge::Old => {}
                    }

                    Some((flat_in_rel.clone(), index_spec.clone()))
                })
            })
            .collect();

        let index_weight: usize = relevant_indices
            .iter()
            .map(|(_flat_in_rel, index)| index.order.len())
            .sum();
        let weight = el_lookup_weight + index_weight;

        writedoc! {f, r#"
            #[allow(unused)]
            const {static_name}: usize = {weight};
        "#}
    })
}

fn display_theory_struct<'a>(
    name: &'a str,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let index_fields = index_set(index_selection)
            .into_iter()
            .map(|(rel, index)| {
                FmtFn(move |f| {
                    let index_name = display_index_field_name(&rel, &index, eqlog, identifiers);
                    let index_type = display_index_type(&rel, eqlog);
                    write!(f, "{index_name}: {index_type},")
                })
            })
            .format("\n");
        let element_index_fields = eqlog
            .iter_rel()
            .map(|rel| {
                let arity: Vec<Type> = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog)
                    .into_iter()
                    .collect();
                let arity_len = arity.len();
                let arity_set: BTreeSet<Type> = arity.iter().copied().collect();
                arity_set
                    .into_iter()
                    .map(move |typ| {
                        FmtFn(move |f| {
                            let field_name =
                                display_element_index_field_name(rel, typ, eqlog, identifiers);
                            write!(f, "{field_name}: BTreeMap<u32, Vec<[u32; {arity_len}]>>,")
                        })
                    })
                    .format("\n")
            })
            .format("\n");

        let type_fields = eqlog
            .iter_type()
            .map(|typ| {
                let typ = display_type(typ, eqlog, identifiers).to_string();
                display_sort_fields(typ)
            })
            .format("\n");

        writedoc! {f, "
            /// A model of the `{name}` theory.
            pub struct {name} {{
                {index_fields}
                {element_index_fields}
                {type_fields}
                empty_join_is_dirty: bool,
            }}
            type Model = {name};
        "}
    })
}

fn display_theory_impl<'a>(
    name: &'a str,
    ram_modules: &'a [RamModule],
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        writeln!(f, "impl {} {{", name)?;

        let new_fn = display_new_fn(eqlog, identifiers, index_selection);
        write!(f, "{}", new_fn)?;
        writeln!(f, "")?;

        let close_fn = display_close_fn();
        write!(f, "{}", close_fn)?;

        let close_until_fn = display_close_until_fn(ram_modules, eqlog, identifiers);
        write!(f, "{}", close_until_fn)?;

        for typ in eqlog.iter_type() {
            let type_name = display_type(typ, eqlog, identifiers)
                .to_string()
                .to_case(UpperCamel);

            let iter_sort_fn = display_iter_type_fn(typ, eqlog, identifiers, index_selection);
            write!(f, "{}", iter_sort_fn)?;

            let root_fn = display_root_fn(type_name.as_str());
            write!(f, "{}", root_fn)?;

            let are_equal_fn = display_are_equal_fn(type_name.as_str());
            write!(f, "{}", are_equal_fn)?;

            writeln!(f, "")?;
        }

        for typ in eqlog.iter_type() {
            let new_element_fn_internal = display_new_element_fn_internal(typ, eqlog, identifiers);
            writeln!(f, "{new_element_fn_internal}")?;

            let equate_elements = display_equate_elements(typ, eqlog, identifiers);
            write!(f, "{}", equate_elements)?;
        }

        for typ in eqlog.iter_type() {
            if eqlog.is_normal_type(typ) || eqlog.is_model_type(typ) {
                let new_el_fn = display_new_element_fn(typ, eqlog, identifiers);
                writeln!(f, "{new_el_fn}")?;
            } else if eqlog.is_enum_type(typ) {
                let type_def_sym_scope = eqlog.type_definition_symbol_scope(typ).unwrap();
                let enum_node = eqlog
                    .iter_enum_decl()
                    .find_map(|(enum_node, ident, _)| {
                        let typ0 = eqlog.semantic_type(type_def_sym_scope, ident)?;
                        if eqlog.are_equal_type(typ0, typ) {
                            Some(enum_node)
                        } else {
                            None
                        }
                    })
                    .unwrap();
                let new_enum_el_fn = display_new_enum_element(enum_node, eqlog, identifiers);
                let enum_cases_fn = display_enum_cases_fn(enum_node, eqlog, identifiers);
                writedoc! {f, "
                    {new_enum_el_fn}
                    {enum_cases_fn}
                "}?;
            } else {
                unreachable!("Unhandled type kind");
            }
        }

        for func in eqlog.iter_func() {
            let rel = eqlog.func_rel(func).unwrap();
            let eval_fn = display_pub_function_eval_fn(func, eqlog, identifiers, index_selection);
            write!(f, "{eval_fn}")?;

            let iter_fn = display_pub_iter_fn(rel, eqlog, identifiers, index_selection);
            write!(f, "{}", iter_fn)?;

            let insert_relation =
                display_pub_insert_relation(rel, eqlog, identifiers, index_selection, true);
            write!(f, "{}", insert_relation)?;

            writeln!(f, "")?;
        }

        for func in eqlog.iter_func() {
            if eqlog.function_can_be_made_defined(func) {
                let define_fn = display_define_fn(func, eqlog, identifiers);
                write!(f, "{}", define_fn)?;
            }
        }

        for pred in eqlog.iter_pred() {
            let rel = eqlog.pred_rel(pred).unwrap();
            let arity = type_list_vec(eqlog.flat_arity(rel).unwrap(), eqlog);
            let arity: Vec<String> = arity
                .into_iter()
                .map(|typ| display_type(typ, eqlog, identifiers).to_string())
                .collect();
            let arity: Vec<&str> = arity.iter().map(|s| s.as_str()).collect();

            let predicate_holds_fn =
                display_pub_predicate_holds_fn(rel, eqlog, identifiers, index_selection);
            write!(f, "{}", predicate_holds_fn)?;

            if !arity.is_empty() {
                let iter_fn = display_pub_iter_fn(rel, eqlog, identifiers, index_selection);
                write!(f, "{}", iter_fn)?;
            }

            let insert_relation =
                display_pub_insert_relation(rel, eqlog, identifiers, index_selection, false);
            write!(f, "{}", insert_relation)?;

            writeln!(f, "")?;
        }

        let canonicalize_fn = display_canonicalize_fn(eqlog, identifiers, index_selection);
        write!(f, "{canonicalize_fn}\n")?;

        let is_dirty_fn = display_is_dirty_fn(eqlog, identifiers, index_selection);
        write!(f, "{}", is_dirty_fn)?;

        writeln!(f, "")?;

        let move_new_to_old_fn = display_move_new_to_old_fn(eqlog, identifiers, index_selection);
        write!(f, "{move_new_to_old_fn}")?;

        write!(f, "}}")?;
        Ok(())
    })
}

fn display_rule_modules<'a>(
    ram_modules: &'a [RamModule],
    index_selection: &'a IndexSelection,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    ram_modules
        .iter()
        .map(move |ram_module| {
            FmtFn(move |f| {
                let lib = display_ram_module(
                    ram_module,
                    index_selection,
                    eqlog,
                    identifiers,
                    symbol_prefix,
                );
                let ram_module_name = ram_module.name.as_str();
                writedoc! {f, "
                    mod {ram_module_name} {{
                        {lib}
                    }}
                "}
            })
        })
        .format("\n")
}

pub fn display_module<'a>(
    name: &'a str,
    eqlog: &'a Eqlog,
    identifiers: &'a BTreeMap<Ident, String>,
    ram_modules: &'a [RamModule],
    index_selection: &'a IndexSelection,
    symbol_prefix: &'a str,
    build_type: BuildType,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let imports = display_imports();
        write!(f, "{}", imports)?;
        write!(f, "\n")?;

        match build_type {
            BuildType::Component => {}
            BuildType::Module => {
                display_rule_modules(
                    ram_modules,
                    index_selection,
                    eqlog,
                    identifiers,
                    symbol_prefix,
                )
                .fmt(f)?;
            }
        }

        let module_env_structs = ram_modules
            .iter()
            .map(|ram_module| display_module_env_struct(ram_module, eqlog, identifiers))
            .format("\n");
        writeln!(f, "{module_env_structs}")?;

        let rule_eval_fns = ram_modules
            .iter()
            .map(|ram_module| display_module_main_fn_decl(ram_module, symbol_prefix))
            .format("\n");
        writedoc! {f, r#"
            unsafe extern "Rust" {{
                {rule_eval_fns}
            }}
        "#}?;

        for rel in eqlog.iter_rel() {
            let weight_static = display_weight_static(rel, index_selection, eqlog, identifiers);
            write!(f, "{weight_static}")?;
        }

        for typ in eqlog.iter_type() {
            let type_camel = display_type(typ, eqlog, identifiers)
                .to_string()
                .to_case(UpperCamel);
            let sort_struct = display_sort_struct(type_camel.as_str());
            write!(f, "{}", sort_struct)?;
            let sort_impl = display_sort_impl(type_camel.as_str());
            write!(f, "{}", sort_impl)?;
        }
        write!(f, "\n")?;

        for (enum_decl, _, _) in eqlog.iter_enum_decl() {
            writeln!(f, "{}", display_enum(enum_decl, eqlog, identifiers))?;
        }

        for func in eqlog.iter_func() {
            let func_args_struct = display_func_args_struct(func, eqlog, identifiers);
            writeln!(f, "{func_args_struct}")?;
        }

        write!(f, "\n")?;

        let model_delta_struct = display_model_delta_struct(eqlog, identifiers);
        write!(f, "{}", model_delta_struct)?;

        let theory_struct = display_theory_struct(name, eqlog, identifiers, index_selection);
        write!(f, "{}", theory_struct)?;

        let model_delta_impl = display_model_delta_impl(eqlog, identifiers);
        write!(f, "{}", model_delta_impl)?;
        write!(f, "\n")?;

        let theory_impl =
            display_theory_impl(name, ram_modules, eqlog, identifiers, index_selection);
        write!(f, "{}", theory_impl)?;

        Ok(())
    })
}
