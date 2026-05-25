mod context;
mod flat_eqlog;
mod rule;
mod types;

pub(crate) use context::RustGenCtx;
pub use rule::*;
pub use types::*;

use crate::algebra::signature::{FuncId, TypeId, TypeKind};
use crate::ast::EnumDeclId;
use crate::flat_eqlog::*;
use crate::fmt_util::*;
use crate::ram::*;
use convert_case::{Case, Casing};
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

fn display_func(func: FuncId, ctx: &RustGenCtx<'_>) -> String {
    ctx.func_name(func).to_case(Snake)
}

pub(crate) fn display_type<'a>(typ: TypeId, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| write!(f, "{}", ctx.type_name(typ)))
}

pub(crate) fn display_rel(rel: FlatRel, ctx: &RustGenCtx<'_>) -> String {
    ctx.rel_name(rel)
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
            #[allow(unused)]
            use std::cell::LazyCell;
            #[allow(unused)]
            use std::ops::DerefMut;
        "}
    })
}

// #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
// pub struct TypeName(pub u32);
fn display_type_struct<'a>(typ: TypeId, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let type_name = display_type(typ, ctx).to_string().to_case(UpperCamel);
        writedoc! {f, "
            #[allow(dead_code)]
            #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
            pub struct {type_name}(pub u32);
        "}
    })
}

fn display_type_impl<'a>(typ: TypeId, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let type_name = display_type(typ, ctx).to_string().to_case(UpperCamel);
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

fn display_ctor<'a>(ctor: crate::ast::CtorDeclId, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let ctor_name: String = ctx.ast().ctor_decl(ctor).name.to_case(UpperCamel);
        let ctor_func = ctx
            .signature()
            .func_for_ctor_decl(ctor)
            .expect("constructor declaration should have a function id");
        let domain = flat_domain(ctor_func, ctx.signature());

        let domain = domain
            .into_iter()
            .map(|typ| display_type(typ, ctx))
            .format(", ");

        write!(f, "{}({})", ctor_name, domain)
    })
}

fn display_enum<'a>(enum_decl: EnumDeclId, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f: &mut Formatter| -> Result {
        let ctors = ctx
            .ast()
            .enum_decl(enum_decl)
            .ctors
            .iter()
            .copied()
            .map(|ctor| format!("{},\n", display_ctor(ctor, ctx)))
            .format("");

        let enum_name = ctx.ast().enum_decl(enum_decl).name.to_case(UpperCamel);

        writedoc! {f, "
            #[allow(unused)]
            #[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
            pub enum {enum_name}Case {{
            {ctors}
            }}
        "}
    })
}

fn display_func_args_struct<'a>(func: FuncId, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel = FlatRel::Func(func);
        let func_camel = display_rel(rel, ctx).to_string().to_case(UpperCamel);
        let dom = flat_domain(func, ctx.signature());
        let args = dom
            .iter()
            .copied()
            .map(|typ| {
                FmtFn(move |f| {
                    let type_camel = display_type(typ, ctx).to_string().to_case(UpperCamel);
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

fn display_type_fields<'a>(typ: TypeId, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let typ = display_type(typ, ctx).to_string();
        let type_snake = typ.to_case(Snake);
        writedoc! {f, "
            {type_snake}_equalities: Unification<{typ}>,
            {type_snake}_weights: Vec<usize>,
            {type_snake}_uprooted: Vec<{typ}>,
        "}
    })
}

fn display_is_dirty_fn<'a>(
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let sets_dirty = iter_flat_rels(ctx.signature())
            .map(FlatInRel::Rel)
            .chain(ctx.signature().iter_types().map(FlatInRel::TypeSet))
            .map(|rel: FlatInRel| {
                FmtFn(move |f| {
                    let query_spec = QuerySpec::all_new();

                    // See index_selection.rs for why the expectations hold.
                    let index = index_selection
                        .queries
                        .get(&(rel.clone(), query_spec))
                        .expect("should have indices for all new tuples in every type/relation")
                        .as_slice();
                    assert!(
                        index.len() == 1,
                        "Expected exactly one index for dirty tuples"
                    );

                    let field_name = display_own_index_field_name(&rel, &index[0], ctx);
                    write!(f, "|| !self.{field_name}.is_empty()")
                })
            })
            .format("\n");

        let uprooted_dirty = ctx
            .signature()
            .iter_types()
            .map(|typ| {
                FmtFn(move |f| {
                    let type_snake = display_type(typ, ctx).to_string().to_case(Snake);
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

fn display_dependent_type_checks<'a>(
    rel: FlatRel,
    arity_types: &'a [TypeId],
    rel_args: &'a [ElVar],
    checked_len: usize,
    ctx: &'a RustGenCtx<'_>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        assert!(checked_len <= arity_types.len());
        assert_eq!(arity_types.len(), rel_args.len());

        if let FlatRel::Func(func) = rel {
            if let Some(member_type) = ctx.signature().type_for_mor_app_func(func) {
                let flat_dom_len = flat_domain(func, ctx.signature()).len();
                assert!(flat_dom_len >= 2);
                let mor_pos = flat_dom_len - 2;
                let arg_pos = flat_dom_len - 1;
                let result_pos = flat_dom_len;

                let parent_model_type = ctx
                    .signature()
                    .type_(member_type)
                    .parents
                    .last()
                    .copied()
                    .expect("mor_app member type should have a parent model");
                let model_ids = ctx
                    .signature()
                    .ids_for_model_type(parent_model_type)
                    .expect("member parent should be a model type");
                let dom_func = display_func(model_ids.dom, ctx);
                let cod_func = display_func(model_ids.cod, ctx);
                let member_rel = display_rel(FlatRel::ModelMember(member_type), ctx);
                let mor_func_args = rel_args[..=mor_pos].iter().format(", ").to_string();

                if checked_len > arg_pos {
                    let arg_expr = &rel_args[arg_pos];
                    writedoc! {f, "
                        let dependent_parent_{arg_pos} = self.{dom_func}({mor_func_args})
                            .expect(\"invalid dependent argument: morphism application requires a defined domain\");
                        assert!(
                            self.{member_rel}(dependent_parent_{arg_pos}, {arg_expr}),
                            \"invalid dependent argument: morphism application argument is not a member of the morphism domain\"
                        );
                    "}?;
                }

                if checked_len > result_pos {
                    let result_expr = &rel_args[result_pos];
                    writedoc! {f, "
                        let dependent_parent_{result_pos} = self.{cod_func}({mor_func_args})
                            .expect(\"invalid dependent argument: morphism application requires a defined codomain\");
                        assert!(
                            self.{member_rel}(dependent_parent_{result_pos}, {result_expr}),
                            \"invalid dependent argument: morphism application result is not a member of the morphism codomain\"
                        );
                    "}?;
                }

                return Ok(());
            }
        }

        if rel.is_model_membership_relation() {
            return Ok(());
        }

        let Some(parent_model_type) = rel.parent_model_type(ctx.signature()) else {
            return Ok(());
        };
        assert_eq!(
            arity_types.first().copied(),
            Some(parent_model_type),
            "member relations should be flattened with the parent model first"
        );
        let parent_expr = &rel_args[0];

        for pos in 1..checked_len {
            let typ = arity_types[pos];
            if ctx.signature().type_(typ).parents.last().copied() != Some(parent_model_type) {
                continue;
            }

            let member_rel = display_rel(FlatRel::ModelMember(typ), ctx);
            let member_expr = &rel_args[pos];
            writedoc! {f, "
                assert!(
                    self.{member_rel}({parent_expr}, {member_expr}),
                    \"invalid dependent argument: element is not a member of the supplied parent model\"
                );
            "}?;
        }

        Ok(())
    })
}

fn display_pub_predicate_holds_fn<'a>(
    rel: FlatRel,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let relation_snake = display_rel(rel, ctx).to_string().to_case(Snake);
        let arity_types = rel.arity(ctx.signature());
        let arity_camel: Vec<String> = arity_types
            .iter()
            .map(|&typ| display_type(typ, ctx).to_string().to_case(UpperCamel))
            .collect();

        let rel_fn_args = arity_camel
            .iter()
            .enumerate()
            .format_with("", |(i, s), f| f(&format_args!(", mut arg{i}: {s}")));

        let canonicalize = arity_camel
            .iter()
            .enumerate()
            .format_with("\n", |(i, s), f| {
                let type_snake = s.to_case(Snake);
                f(&format_args!("arg{i} = self.root_{type_snake}(arg{i});"))
            });

        let rel_args: Vec<ElVar> = (0..arity_types.len())
            .map(|i| ElVar {
                name: format!("arg{i}").into(),
            })
            .collect();
        let dependent_checks =
            display_dependent_type_checks(rel, &arity_types, &rel_args, arity_types.len(), ctx);

        let rel_args_doc =
            (0..arity_types.len()).format_with(", ", |i, f| f(&format_args!("arg{i}")));

        let rel = FlatInRel::Rel(rel);
        let query = QuerySpec::one(rel.clone(), ctx.signature());
        let indices = index_selection
            .queries
            .get(&(rel.clone(), query))
            .expect("should have indices for relation")
            .as_slice();
        let rel = &rel;

        let checks = indices
            .into_iter()
            .map(|index_spec| {
                let index_expr = display_index_expr(rel, &index_spec, ctx);
                let IndexSpec { order, age: _ } = index_spec;
                let row_args = order
                    .iter()
                    .map(|i| FmtFn(move |f| write!(f, "arg{i}.0")))
                    .format(", ");
                FmtFn(move |f| write!(f, "|| {index_expr}.contains([{row_args}])"))
            })
            .format("\n");

        writedoc! {f, "
            /// Returns `true` if `{relation_snake}({rel_args_doc})` holds.
            #[allow(dead_code)]
            pub fn {relation_snake}(&self{rel_fn_args}) -> bool {{
            {canonicalize}
            {dependent_checks}

            false
            {checks}
            }}
        "}
    })
}

fn display_pub_function_eval_fn<'a>(
    func: FuncId,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel = FlatRel::Func(func);

        let relation_snake = display_rel(rel, ctx).to_string().to_case(Snake);
        let relation_snake = relation_snake.as_str();

        let flat_dom = flat_domain(func, ctx.signature());
        let flat_dom_len = flat_dom.len();

        let cod = ctx.signature().func(func).codomain;
        let cod_camel = display_type(cod, ctx).to_string().to_case(UpperCamel);
        let cod_camel = &cod_camel;

        let params = flat_dom
            .iter()
            .copied()
            .enumerate()
            .map(|(i, typ)| {
                FmtFn(move |f| {
                    let type_camel = display_type(typ, ctx).to_string().to_case(UpperCamel);
                    write!(f, "mut arg{i}: {type_camel}, ")
                })
            })
            .format("");

        let canonicalize = flat_dom
            .iter()
            .copied()
            .enumerate()
            .map(|(i, typ)| {
                FmtFn(move |f| {
                    let type_snake = display_type(typ, ctx).to_string().to_case(Snake);
                    write!(f, "arg{i} = self.root_{type_snake}(arg{i});")
                })
            })
            .format("\n");

        let rel_args: Vec<ElVar> = (0..=flat_dom_len)
            .map(|i| ElVar {
                name: format!("arg{i}").into(),
            })
            .collect();
        let mut arity_types = flat_dom.clone();
        arity_types.push(cod);
        let dependent_checks =
            display_dependent_type_checks(rel, &arity_types, &rel_args, flat_dom_len, ctx);

        let doc_args = (0..flat_dom.len())
            .map(|i| FmtFn(move |f| write!(f, "arg{i}")))
            .format(", ")
            .to_string();

        let query_spec = QuerySpec::eval_func(func, ctx.signature());
        let flat_in_rel = FlatInRel::Rel(FlatRel::Func(func));

        let indices = index_selection
            .queries
            .get(&(flat_in_rel.clone(), query_spec))
            .unwrap();

        let flat_in_rel = &flat_in_rel;

        let or_else_get_from = indices
            .into_iter()
            .map(move |index| {
                FmtFn(move |f| {
                    let index_expr = display_index_expr(&flat_in_rel, &index, ctx);
                    assert_eq!(*index.order.last().unwrap(), flat_dom_len);

                    let gets = index.order[0..index.order.len() - 1]
                        .iter()
                        .map(|i| FmtFn(move |f| write!(f, "let set = set.get(arg{i}.0)?;")))
                        .format("\n");
                    writedoc! {f, "
                        .or_else(move || -> Option<u32> {{
                            #[allow(unused_parens)]
                            let set = {index_expr};
                            {gets}
                            let [result] = set.iter().next()?;
                            Some(result)
                        }})
                    "}
                })
            })
            .format("\n");

        let result = "result.map(|x| x.into())";

        writedoc! {f, "
            /// Evaluates `{relation_snake}({doc_args})`.
            #[allow(dead_code)]
            pub fn {relation_snake}(&self, {params}) -> Option<{cod_camel}> {{
            {canonicalize}
            {dependent_checks}

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
    rel: FlatRel,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let is_function = matches!(rel, FlatRel::Func(_));
        let relation = display_rel(rel, ctx);
        let rel_snake = display_rel(rel, ctx).to_string().to_case(Snake);
        let rel_snake = rel_snake.as_str();
        let arity_tys = rel.arity(ctx.signature());
        let arity_tys = &arity_tys;
        let arity: Vec<String> = arity_tys
            .iter()
            .map(move |ty| display_type(*ty, ctx).to_string().to_case(UpperCamel))
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

        let flat_in_rel = FlatInRel::Rel(rel);
        let query_spec = QuerySpec::all();
        let indices = index_selection
            .queries
            .get(&(flat_in_rel.clone(), query_spec))
            .expect("should have indices for relation")
            .as_slice();

        let index_its = indices
            .into_iter()
            .enumerate()
            .map(move |(i, index)| {
                let flat_in_rel = flat_in_rel.clone();
                FmtFn(move |f| {
                    let flat_in_rel = flat_in_rel.clone();
                    let index_expr = display_index_expr(&flat_in_rel, &index, ctx);
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
                                let type_camel =
                                    display_type(*typ, ctx).to_string().to_case(UpperCamel);
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
                        {index_expr}
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
    rel: FlatRel,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl 'a + Display {
    index_selection
        .indices
        .iter()
        .flat_map(|(rel, indices)| {
            indices
                .iter()
                .map(move |index| (rel.clone(), index.clone()))
        })
        .filter(move |(flat_in_rel, index)| {
            if index.age != age {
                return false;
            }

            match flat_in_rel {
                FlatInRel::Rel(r0) => *r0 == rel,
                FlatInRel::RelWithDiagonals {
                    rel: r0,
                    equalities: _,
                } => *r0 == rel,
                FlatInRel::Equality(_) | FlatInRel::TypeSet(_) => false,
            }
        })
        .map(move |(flat_in_rel, index)| {
            FmtFn(move |f| {
                let index_name = display_index_field_name(&flat_in_rel, &index, ctx);
                if let FlatInRel::RelWithDiagonals { rel: _, equalities } = &flat_in_rel {
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
                        .format(", ")
                        .to_string();

                    if flat_in_rel.parent_model_type(ctx.signature()).is_some() {
                        writedoc! {f, "
                            if {checks} {{
                            self.{index_name}_own.insert([{args}]);
                            self.{index_name}_all.insert([{args}]);
                            }}
                        "}
                    } else {
                        writedoc! {f, "
                            if {checks} {{
                            self.{index_name}.insert([{args}]);
                            }}
                        "}
                    }
                } else {
                    // No diagonals.
                    let args = index
                        .order
                        .iter()
                        .map(|i| args[*i].clone())
                        .format(", ")
                        .to_string();
                    if flat_in_rel.parent_model_type(ctx.signature()).is_some() {
                        writedoc! {f, "
                            self.{index_name}_own.insert([{args}]);
                            self.{index_name}_all.insert([{args}]);
                        "}
                    } else {
                        writedoc! {f, "
                            self.{index_name}.insert([{args}]);
                        "}
                    }
                }
            })
        })
        .format("\n")
}

fn display_pub_insert_relation<'a>(
    rel: FlatRel,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
    is_function: bool,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, ctx).to_string().to_case(Snake);
        let rel_snake = rel_snake.as_str();

        let arity_types = rel.arity(ctx.signature());
        let arity_camel: Vec<String> = arity_types
            .iter()
            .map(|&typ| display_type(typ, ctx).to_string().to_case(UpperCamel))
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
                    let type_snake = display_type(*typ, ctx).to_string().to_case(Snake);
                    write!(f, "let {arg} = self.root_{type_snake}({arg});")
                })
            })
            .format("\n");

        let dependent_checks =
            display_dependent_type_checks(rel, &arity_types, rel_args, arity_types.len(), ctx);

        let unwrap_args = rel_args
            .iter()
            .cloned()
            .map(|arg| {
                FmtFn(move |f: &mut Formatter| -> Result { write!(f, "let {arg}: u32 = {arg}.0;") })
            })
            .format("\n");

        let weight_static_name = display_weight_static_name(rel, ctx).to_string();
        let update_weights = rel_args
            .iter()
            .cloned()
            .zip(arity_types.iter())
            .enumerate()
            .map(move |(i, (arg, typ))| {
                let weight_static_name = weight_static_name.clone();
                FmtFn(move |f: &mut Formatter| -> Result {
                    let type_snake = display_type(*typ, ctx)
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

        let index_inserts =
            display_insert_row_block(rel_args, IndexAge::New, rel, ctx, index_selection);

        let flat_rel = FlatInRel::Rel(rel);
        let contains_query = QuerySpec::one(flat_rel.clone(), ctx.signature());
        let contains_indices = index_selection
            .queries
            .get(&(flat_rel.clone(), contains_query))
            .expect("should have indices for relation")
            .as_slice();

        let flat_rel = &flat_rel;
        let contains_checks = contains_indices
            .into_iter()
            .map(|index_spec| {
                let index_expr = display_index_expr(flat_rel, &index_spec, ctx);
                let IndexSpec { order, age: _ } = index_spec;
                let row_args = order.iter().map(|i| rel_args[*i].clone()).format(", ");
                FmtFn(move |f| {
                    writedoc! {f, "
                        if {index_expr}.contains([{row_args}]) {{
                        return;
                        }}
                    "}
                })
            })
            .format("\n");

        let mut type_positions: BTreeMap<TypeId, Vec<usize>> = BTreeMap::new();
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
                                display_element_index_field_name(rel, *typ, ctx).to_string();
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
                {dependent_checks}
                {unwrap_args}

                {contains_checks}

                {index_inserts}

                {el_index_inserts}

                {update_weights}
            }}
        "}
    })
}

fn display_new_element_fn_internal<'a>(
    typ: TypeId,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let type_camel = display_type(typ, ctx).to_string().to_case(UpperCamel);
        let type_snake = type_camel.to_case(Snake);
        let type_snake = type_snake.as_str();

        let parent_type = ctx.signature().type_(typ).parents.last().copied();
        let parent_param = FmtFn(move |f| {
            let Some(parent_type) = parent_type else {
                return Ok(());
            };
            write!(f, "parent: {}", display_type(parent_type, ctx))
        });

        let insert_parent = FmtFn(move |f| {
            if parent_type.is_none() {
                return Ok(());
            }
            let parent_pred = display_rel(FlatRel::ModelMember(typ), ctx);

            write!(f, "self.insert_{parent_pred}(parent, el.into());")
        });

        let type_set_rel = FlatInRel::TypeSet(typ);
        let new_index = index_selection
            .indices
            .get(&type_set_rel)
            .expect("type set should have indices")
            .iter()
            .filter(|index| index.age == IndexAge::New)
            .exactly_one()
            .expect("should have exactly one new index for type set");

        let new_index_field = display_index_field_name(&type_set_rel, new_index, ctx);

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

fn display_new_element_fn<'a>(typ: TypeId, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let type_camel = display_type(typ, ctx).to_string().to_case(UpperCamel);
        let type_snake = type_camel.to_case(Snake);

        let parent_type = ctx.signature().type_(typ).parents.last().copied();
        let parent_param = FmtFn(move |f| {
            let Some(parent_type) = parent_type else {
                return Ok(());
            };
            write!(f, "parent: {}", display_type(parent_type, ctx))
        });

        let parent_arg = FmtFn(move |f| {
            if parent_type.is_none() {
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
    enum_decl: EnumDeclId,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f: &mut Formatter| -> Result {
        let enum_name = &ctx.ast().enum_decl(enum_decl).name;
        let enum_name_camel = enum_name.to_case(UpperCamel);
        let enum_name_camel = enum_name_camel.as_str();
        let enum_name_snake = enum_name.to_case(Snake);

        let ctors = ctx.ast().enum_decl(enum_decl).ctors.iter().copied();

        let match_branches = ctors
            .map(|ctor| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let ctor_name = &ctx.ast().ctor_decl(ctor).name;
                    let ctor_name_snake = ctor_name.to_case(Snake);
                    let ctor_name_camel = ctor_name.to_case(UpperCamel);

                    let ctor_func = ctx
                        .signature()
                        .func_for_ctor_decl(ctor)
                        .expect("constructor declaration should have a function id");
                    let ctor_arg_types = flat_domain(ctor_func, ctx.signature());
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

fn display_enum_cases_fn<'a>(enum_decl: EnumDeclId, ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    FmtFn(move |f: &mut Formatter| -> Result {
        let enum_name = &ctx.ast().enum_decl(enum_decl).name;
        let enum_name_camel = enum_name.to_case(UpperCamel);
        let enum_name_camel = enum_name_camel.as_str();
        let enum_name_snake = enum_name.to_case(Snake);

        let ctors = ctx.ast().enum_decl(enum_decl).ctors.iter().copied();

        let ctor_value_iters = ctors
            .map(|ctor| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let ctor_name = &ctx.ast().ctor_decl(ctor).name;
                    let ctor_name_snake = ctor_name.to_case(Snake);
                    let ctor_name_camel = ctor_name.to_case(UpperCamel);

                    let ctor_func = ctx
                        .signature()
                        .func_for_ctor_decl(ctor)
                        .expect("constructor declaration should have a function id");
                    let arg_num = flat_domain(ctor_func, ctx.signature()).len();

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
    typ: TypeId,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let type_camel = format!("{}", display_type(typ, ctx)).to_case(UpperCamel);
        let type_snake = type_camel.to_case(Snake);

        let type_set_rel = FlatInRel::TypeSet(typ);
        let indices = index_selection
            .indices
            .get(&type_set_rel)
            .expect("type set should have indices");

        let index_new = indices
            .iter()
            .filter(|index| index.age == IndexAge::New)
            .exactly_one()
            .expect("should have exactly one new index for type set");
        let index_old = indices
            .iter()
            .filter(|index| index.age == IndexAge::Old)
            .exactly_one()
            .expect("should have exactly one old index for type set");

        let index_new = display_index_field_name(&type_set_rel, index_new, ctx);
        let index_old = display_index_field_name(&type_set_rel, index_old, ctx);

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

fn display_root_fn<'a>(typ: TypeId, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let type_name = display_type(typ, ctx).to_string().to_case(UpperCamel);
        let type_snake = type_name.to_case(Snake);
        writedoc! {f, "
            /// Returns the canonical representative of the equivalence class of `el`.
            #[allow(dead_code)]
            pub fn root_{type_snake}(&self, el: {type_name}) -> {type_name} {{
                if el.0 as usize >= self.{type_snake}_equalities.len() {{
                    el
                }} else {{
                    self.{type_snake}_equalities.root_const(el)
                }}
            }}
        "}
    })
}

fn display_are_equal_fn<'a>(typ: TypeId, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let type_name = display_type(typ, ctx).to_string().to_case(UpperCamel);
        let type_snake = type_name.to_case(Snake);
        writedoc! {f, "
            /// Returns `true` if `lhs` and `rhs` are in the same equivalence class.
            #[allow(dead_code)]
            pub fn are_equal_{type_snake}(&self, lhs: {type_name}, rhs: {type_name}) -> bool {{
                self.root_{type_snake}(lhs) == self.root_{type_snake}(rhs)
            }}
        "}
    })
}

fn display_iter_type_fn<'a>(
    typ: TypeId,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let type_snake = display_type(typ, ctx).to_string().to_case(Snake);
        let type_camel = type_snake.to_case(UpperCamel);
        let rel = FlatInRel::TypeSet(typ);
        let query = QuerySpec::all();
        let indices = index_selection.queries.get(&(rel.clone(), query)).unwrap();

        let index_chain_iter = indices
            .into_iter()
            .map(move |index| {
                assert_eq!(index.order.len(), 1);

                let rel = rel.clone();
                FmtFn(move |f| {
                    let index_field = display_index_field_name(&rel, index, ctx);
                    writedoc! {f, "
                        .chain(self.{index_field}.iter())
                    "}
                })
            })
            .format("\n");

        writedoc! {f, "
            /// Returns an iterator over elements of type `{type_camel}`.
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
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let equalities = match &rel {
            FlatInRel::Rel(_) => None,
            FlatInRel::RelWithDiagonals { rel: _, equalities } => Some(equalities),
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

        let field_name = display_own_index_field_name(&rel, &index, ctx);

        write!(f, "self.{field_name}.remove([{permuted_row_args}])")
    })
}

fn display_canonicalize_rel_block<'a>(
    rel: FlatRel,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, ctx).to_string().to_case(Snake);

        let arity = rel.arity(ctx.signature());
        let arity_len = arity.len();
        let types: BTreeSet<_> = arity.iter().copied().collect();
        let row_args: Vec<ElVar> = (0..arity.len()).map(ElVar::from).collect();
        let row_args = row_args.as_slice();

        let fill_non_canonical_rows_vec = types
            .into_iter()
            .map(|typ| {
                FmtFn(move |f| {
                    let type_snake = display_type(typ, ctx).to_string().to_case(Snake);
                    let element_index_field = display_element_index_field_name(rel, typ, ctx);

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
                        let type_i_snake = display_type(type_i, ctx)
                            .to_string()
                            .to_case(Snake);
                        let weight_static_name = display_weight_static_name(rel, ctx);
                        let el = row_args[i].clone();
                        writedoc! {f, "
                            let weight{i}: &mut usize = &mut self.{type_i_snake}_weights[usize::try_from({el}).unwrap()];
                            *weight{i} = weight{i}.saturating_sub({weight_static_name});
                        "}
                    })
                })
                .format("\n");

        let flat_rel = FlatInRel::Rel(rel);
        let primary_new_indices = index_selection
            .queries
            .get(&(flat_rel.clone(), QuerySpec::all_new()))
            .unwrap();
        assert_eq!(primary_new_indices.len(), 1);
        let primary_new_index: IndexSpec = primary_new_indices[0].clone();

        let primary_old_indices = index_selection
            .queries
            .get(&(flat_rel.clone(), QuerySpec::all_old()))
            .unwrap();
        assert_eq!(primary_old_indices.len(), 1);
        let primary_old_index: IndexSpec = primary_old_indices[0].clone();

        let mut secondary_new_indices: BTreeSet<(FlatInRel, IndexSpec)> = BTreeSet::new();
        let mut secondary_old_indices: BTreeSet<(FlatInRel, IndexSpec)> = BTreeSet::new();
        for (r0, indices) in &index_selection.indices {
            match r0 {
                FlatInRel::Rel(_) => {
                    if r0 != &flat_rel {
                        continue;
                    }
                }
                FlatInRel::RelWithDiagonals {
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
                if r0 == &flat_rel {
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
                    let remove_from_index_expr =
                        display_remove_from_index_expr(r.clone(), index.clone(), row_args, ctx);
                    write!(f, "{remove_from_index_expr};")
                })
            })
            .format("\n");
        let remove_from_secondary_old_indices = secondary_old_indices
            .into_iter()
            .map(move |(r, index)| {
                FmtFn(move |f| {
                    let remove_from_index_expr =
                        display_remove_from_index_expr(r.clone(), index.clone(), row_args, ctx);
                    write!(f, "{remove_from_index_expr};")
                })
            })
            .format("\n");

        let remove_from_primary_new_index =
            display_remove_from_index_expr(flat_rel.clone(), primary_new_index, row_args, ctx);
        let remove_from_primary_old_index =
            display_remove_from_index_expr(flat_rel, primary_old_index, row_args, ctx);

        let insert_row_args = row_args
            .iter()
            .zip(arity.iter())
            .map(|(arg, typ)| {
                FmtFn(move |f| {
                    let type_snake = display_type(*typ, ctx).to_string().to_case(UpperCamel);
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
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_blocks = iter_flat_rels(ctx.signature())
            .filter(|rel| rel.is_model_membership_relation())
            .chain(
                iter_flat_rels(ctx.signature()).filter(|rel| !rel.is_model_membership_relation()),
            )
            .map(|rel| {
                FmtFn(move |f| {
                    let block = display_canonicalize_rel_block(rel, ctx, index_selection);
                    let rel = display_rel(rel, ctx);
                    writedoc! {f, "
                        // Canonicalize {rel}.
                        {block}
                    "}
                })
            })
            .format("\n");

        let clear_uprooted_vecs = ctx
            .signature()
            .iter_types()
            .map(|typ| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let type_snake = format!("{}", display_type(typ, ctx)).to_case(Snake);
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

fn display_rel_row_type<'a>(rel: FlatRel, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let arity_len = rel.arity(ctx.signature()).len();
        write!(f, "[u32; {arity_len}]")
    })
}

/// Displays the tuple type of the arguments of a function.
fn display_func_args_type<'a>(func: FuncId, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let arity_len = flat_domain(func, ctx.signature()).len();
        write!(f, "[u32; {arity_len}]")
    })
}

fn display_out_set_field_name<'a>(
    rel: &'a FlatOutRel,
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| match rel {
        FlatOutRel::Rel(rel) => {
            let rel_snake = display_rel(*rel, ctx).to_string().to_case(Snake);
            write!(f, "new_{rel_snake}")
        }
        FlatOutRel::Equality(typ) => {
            let type_snake = display_type(*typ, ctx).to_string().to_case(Snake);
            write!(f, "new_{type_snake}_equalities")
        }
        FlatOutRel::FuncDomain(func) => {
            let rel_snake = display_rel(FlatRel::Func(*func), ctx)
                .to_string()
                .to_case(Snake);
            write!(f, "new_{rel_snake}_def")
        }
    })
}

fn display_out_set_type<'a>(rel: &'a FlatOutRel, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let arity_len = rel.arity(ctx.signature()).len();
        write!(f, "Vec<[u32; {arity_len}]>")
    })
}

fn display_model_delta_struct<'a>(ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    FmtFn(move |f| {
        let new_tuples = iter_flat_rels(ctx.signature())
            .map(|rel| {
                FmtFn(move |f| {
                    let rel_snake = display_rel(rel, ctx).to_string().to_case(Snake);
                    let row_type = display_rel_row_type(rel, ctx);
                    write!(f, "new_{rel_snake}: Vec<{row_type}>,")
                })
            })
            .format("\n");

        let new_equalities = ctx
            .signature()
            .iter_types()
            .map(|typ| {
                FmtFn(move |f| {
                    let type_snake = display_type(typ, ctx).to_string().to_case(Snake);
                    write!(f, "new_{type_snake}_equalities: Vec<[u32; 2]>,")
                })
            })
            .format("\n");

        let new_defines = ctx
            .signature()
            .iter_funcs()
            .filter(|func| ctx.function_can_be_made_defined(*func))
            .map(|func| {
                FmtFn(move |f| {
                    let rel_snake = display_rel(FlatRel::Func(func), ctx)
                        .to_string()
                        .to_case(Snake);
                    let args_type = display_func_args_type(func, ctx);
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

fn display_model_delta_impl<'a>(ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    FmtFn(move |f| {
        writedoc! {f, "
            impl ModelDelta {{
        "}
        .unwrap();

        let new_fn = display_model_delta_new_fn(ctx);
        write!(f, "{}", new_fn).unwrap();

        let apply_equalities_fn = display_model_delta_apply_equalities_fn(ctx);
        write!(f, "{}", apply_equalities_fn).unwrap();

        let apply_tuples_fn = display_model_delta_apply_tuples_fn(ctx);
        write!(f, "{}", apply_tuples_fn).unwrap();

        let apply_def_fn = display_model_delta_apply_def_fn(ctx);
        write!(f, "{}", apply_def_fn).unwrap();

        writedoc! {f, "
            }}
        "}
    })
}

fn display_model_delta_new_fn<'a>(ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    FmtFn(move |f| {
        let new_tuples = iter_flat_rels(ctx.signature())
            .map(|rel| {
                FmtFn(move |f| {
                    let relation_snake = display_rel(rel, ctx).to_string().to_case(Snake);
                    write!(f, "new_{relation_snake}: Vec::new(),")
                })
            })
            .format("\n");

        let new_equalities = ctx
            .signature()
            .iter_types()
            .map(|typ| {
                FmtFn(move |f| {
                    let type_snake = display_type(typ, ctx).to_string().to_case(Snake);
                    write!(f, "new_{type_snake}_equalities: Vec::new(),")
                })
            })
            .format("\n");
        let new_defines = ctx
            .signature()
            .iter_funcs()
            .filter(|&func| ctx.function_can_be_made_defined(func))
            .map(|func| {
                FmtFn(move |f| {
                    let func_snake = display_rel(FlatRel::Func(func), ctx)
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

fn display_model_delta_apply_equalities_fn<'a>(ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    FmtFn(move |f| {
        let type_equalities = ctx
            .signature()
            .iter_types()
            .map(|typ| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let type_snake = format!("{}", display_type(typ, ctx)).to_case(Snake);

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

fn display_model_delta_apply_tuples_fn<'a>(ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let relations = iter_flat_rels(ctx.signature())
            .map(|rel| {
                FmtFn(move |f| {
                    let arity = rel.arity(ctx.signature());
                    let rel_snake = display_rel(rel, ctx).to_string().to_case(Snake);
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

fn display_model_delta_apply_def_fn<'a>(ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    FmtFn(move |f| {
        let func_defs = ctx
            .signature()
            .iter_funcs()
            .filter_map(|func| {
                if !ctx.function_can_be_made_defined(func) {
                    return None;
                }

                let func_name = display_func(func, ctx).to_string();
                let func_snake = func_name.to_case(Snake);

                let domain = flat_domain(func, ctx.signature());

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
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let relations = iter_flat_rels(ctx.signature())
            .map(|rel| {
                FmtFn(move |f| {
                    let flat_rel = FlatInRel::Rel(rel);
                    let query_new = QuerySpec::all_new();
                    let indices_new = index_selection
                        .queries
                        .get(&(flat_rel.clone(), query_new))
                        .expect("should have indices for all new relations");
                    assert!(
                        indices_new.len() == 1,
                        "should have just one index for all new tuples"
                    );
                    let primary_index_new = &indices_new[0];

                    let args: Vec<ElVar> = (0..flat_rel.arity(ctx.signature()).len())
                        .map(ElVar::from)
                        .collect();
                    let primary_new_args = primary_index_new
                        .order
                        .iter()
                        .map(|i| args[*i].clone())
                        .format(", ");

                    let primary_new_index =
                        display_own_index_field_name(&flat_rel, &primary_index_new, ctx);

                    let old_inserts = display_insert_row_block(
                        args.as_slice(),
                        IndexAge::Old,
                        rel,
                        ctx,
                        index_selection,
                    );

                    let new_clears = index_selection
                        .indices
                        .iter()
                        .flat_map(|(rel, indices)| {
                            indices
                                .iter()
                                .map(move |index| (rel.clone(), index.clone()))
                        })
                        .filter(|(flat_in_rel, index)| {
                            match index.age {
                                IndexAge::Old => {
                                    return false;
                                }
                                IndexAge::New => {}
                            }

                            match flat_in_rel {
                                FlatInRel::Rel(rel0) => {
                                    *rel0
                                        == match &flat_rel {
                                            FlatInRel::Rel(rel) => *rel,
                                            _ => unreachable!("flat relation should be a relation"),
                                        }
                                }
                                FlatInRel::RelWithDiagonals { rel: rel0, .. } => {
                                    *rel0
                                        == match &flat_rel {
                                            FlatInRel::Rel(rel) => *rel,
                                            _ => unreachable!("flat relation should be a relation"),
                                        }
                                }
                                FlatInRel::TypeSet(_) => false,
                                FlatInRel::Equality(_) => false,
                            }
                        })
                        .map(move |(flat_in_rel, index)| {
                            FmtFn(move |f| {
                                let field_name =
                                    display_own_index_field_name(&flat_in_rel, &index, ctx);
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

        let types = ctx
            .signature()
            .iter_types()
            .map(|typ| {
                FmtFn(move |f| {
                    let flat_rel = FlatInRel::TypeSet(typ);

                    let indices = index_selection
                        .indices
                        .get(&flat_rel)
                        .expect("type set should have indices");

                    let index_new = indices
                        .iter()
                        .filter(|index| index.age == IndexAge::New)
                        .exactly_one()
                        .expect("should have exactly one new index for type set");
                    let index_old = indices
                        .iter()
                        .filter(|index| index.age == IndexAge::Old)
                        .exactly_one()
                        .expect("should have exactly one old index for type set");

                    let new_index = display_index_field_name(&flat_rel, index_new, ctx);
                    let old_index = display_index_field_name(&flat_rel, index_old, ctx);

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

#[derive(Copy, Clone)]
enum MorphismIndexColumnKind {
    Parent,
    Member(TypeId),
    Copy,
}

impl MorphismIndexColumnKind {
    fn needs_mapping(self) -> bool {
        matches!(
            self,
            MorphismIndexColumnKind::Parent | MorphismIndexColumnKind::Member(_)
        )
    }
}

fn morphism_index_column_kind(
    parent_model_type: TypeId,
    column_index: usize,
    typ: TypeId,
    ctx: &RustGenCtx<'_>,
) -> MorphismIndexColumnKind {
    if column_index == 0 {
        assert_eq!(typ, parent_model_type);
        return MorphismIndexColumnKind::Parent;
    }

    if ctx.signature().type_(typ).parents.last().copied() == Some(parent_model_type) {
        return MorphismIndexColumnKind::Member(typ);
    }

    MorphismIndexColumnKind::Copy
}

fn display_prefix_tree_type(arity_len: usize) -> impl Display {
    FmtFn(move |f| write!(f, "PrefixTree{arity_len}"))
}

fn display_mor_app_map_expr<'a>(
    typ: TypeId,
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let mor_app_func = ctx
            .signature()
            .mor_app_func_for_type(typ)
            .expect("mor_app_func should be defined for member types");
        let mor_app_rel = FlatInRel::Rel(FlatRel::Func(mor_app_func));

        let mor_app_indices = index_selection
            .indices
            .get(&mor_app_rel)
            .expect("mor_app rel should have indices");
        let mor_app_eval_index_new = mor_app_indices
            .iter()
            .filter(|index| index.age == IndexAge::New && index.order.as_ref() == [0, 1, 2])
            .exactly_one()
            .expect("should have exactly one new index with order [0, 1, 2] for mor_app rel");
        let mor_app_eval_index_old = mor_app_indices
            .iter()
            .filter(|index| index.age == IndexAge::Old && index.order.as_ref() == [0, 1, 2])
            .exactly_one()
            .expect("should have exactly one old index with order [0, 1, 2] for mor_app rel");

        let mor_app_eval_index_new_name =
            display_index_field_name(&mor_app_rel, mor_app_eval_index_new, ctx);
        let mor_app_eval_index_old_name =
            display_index_field_name(&mor_app_rel, mor_app_eval_index_old, ctx);

        writedoc! {f, "
            self.{mor_app_eval_index_new_name}
            .get(*morph)
            .unwrap_or_else(|| PrefixTree2::empty())
            .union(
            self.{mor_app_eval_index_old_name}
            .get(*morph)
            .unwrap_or_else(|| PrefixTree2::empty()),
            )
        "}
    })
}

fn display_morphism_index_prefix_walk<'a>(
    columns: &'a [MorphismIndexColumnKind],
    arity_len: usize,
    source_tree: String,
    source_tree_is_ref: bool,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let body = display_morphism_index_prefix_walk_from(
            columns,
            0,
            arity_len,
            source_tree.clone(),
            source_tree_is_ref,
            Vec::new(),
        );
        write!(f, "{body}")
    })
}

fn display_morphism_index_prefix_walk_from(
    columns: &[MorphismIndexColumnKind],
    pos: usize,
    current_dim: usize,
    source_tree: String,
    source_tree_is_ref: bool,
    target_prefix: Vec<String>,
) -> String {
    if pos == columns.len() {
        let target_prefix = target_prefix.iter().format(", ");
        let suffix = if source_tree_is_ref {
            format!("(*{source_tree}).clone()")
        } else {
            format!("{source_tree}.clone()")
        };
        return format!("propagated.push(([{target_prefix}], {suffix}));");
    }

    let el = format!("el{pos}");
    let subtree = format!("{source_tree}_{pos}");
    let subtree_is_ref = current_dim > 1;

    match columns[pos] {
        MorphismIndexColumnKind::Parent => {
            let mut target_prefix = target_prefix;
            target_prefix.push("*cod".to_string());
            let body = display_morphism_index_prefix_walk_from(
                columns,
                pos + 1,
                current_dim - 1,
                subtree.clone(),
                true,
                target_prefix,
            );
            formatdoc! {"
                let {subtree} = match {source_tree}.get(*dom) {{
                    Some({subtree}) => {subtree},
                    None => {{ continue; }},
                }};
                {body}
            "}
        }
        MorphismIndexColumnKind::Member(_) => {
            let mut target_prefix = target_prefix;
            target_prefix.push(format!("mapped_{el}"));
            let body = display_morphism_index_prefix_walk_from(
                columns,
                pos + 1,
                current_dim - 1,
                subtree.clone(),
                subtree_is_ref,
                target_prefix,
            );
            formatdoc! {"
                for ({el}, {subtree}) in {source_tree}.iter_restrictions() {{
                    let Some(mapped_{el}) = map_{el}
                        .get({el})
                        .and_then(|restriction| restriction.iter().next().map(|[mapped]| mapped))
                    else {{
                        continue;
                    }};
                    {body}
                }}
            "}
        }
        MorphismIndexColumnKind::Copy => {
            let mut target_prefix = target_prefix;
            target_prefix.push(el.clone());
            let body = display_morphism_index_prefix_walk_from(
                columns,
                pos + 1,
                current_dim - 1,
                subtree.clone(),
                subtree_is_ref,
                target_prefix,
            );
            formatdoc! {"
                for ({el}, {subtree}) in {source_tree}.iter_restrictions() {{
                    {body}
                }}
            "}
        }
    }
}

fn display_apply_morphism_index_propagated<'a>(
    index_field_name: &'a str,
    arity_len: usize,
    prefix_len: usize,
    suffix_len: usize,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let prefix_vars = (0..prefix_len)
            .map(|i| FmtFn(move |f| write!(f, "el{i}")))
            .format(", ");
        let wrap_suffix = (1..prefix_len)
            .rev()
            .map(|i| {
                let tree_type = display_prefix_tree_type(arity_len - i);
                FmtFn(move |f| {
                    writedoc! {f, "
                        let mapped_dom_set = {{
                            let mut tree = {tree_type}::new();
                            tree.insert_restriction(el{i}, mapped_dom_set);
                            tree
                        }};
                    "}
                })
            })
            .format("\n");

        let suffix_type = display_prefix_tree_type(suffix_len);
        writedoc! {f, "
            for ([{prefix_vars}], mapped_dom_set) in propagated {{
                let mapped_dom_set: {suffix_type} = mapped_dom_set;
                {wrap_suffix}
                {index_field_name}_own.remove_restriction(el0, &mapped_dom_set);
                {index_field_name}_all.insert_restriction(el0, mapped_dom_set);
            }}
        "}
    })
}

fn display_recompute_model_indices_fn<'a>(
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let compute_ordered_mor_vars = ctx
            .signature()
            .iter_types()
            .filter(|typ| matches!(ctx.signature().type_(*typ).kind, TypeKind::Model))
            .map(|typ| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let ids = ctx
                        .signature()
                        .ids_for_model_type(typ)
                        .expect("typ is model type");
                    let type_snake = display_type(typ, ctx).to_string().to_case(Snake);

                    let dom_rel = FlatInRel::Rel(FlatRel::Func(ids.dom));
                    let cod_rel = FlatInRel::Rel(FlatRel::Func(ids.cod));
                    let set_rel = FlatInRel::TypeSet(typ);

                    let dom_indices = index_selection
                        .indices
                        .get(&dom_rel)
                        .expect("dom rel should have indices");
                    let new_order_1_0 = dom_indices
                        .iter()
                        .filter(|index| index.age == IndexAge::New && index.order.as_ref() == [1, 0])
                        .exactly_one()
                        .expect("should have exactly one new index with order [1, 0] for dom rel");
                    let old_order_1_0 = dom_indices
                        .iter()
                        .filter(|index| index.age == IndexAge::Old && index.order.as_ref() == [1, 0])
                        .exactly_one()
                        .expect("should have exactly one old index with order [1, 0] for dom rel");

                    let dom_new_order_1_0 =
                        display_index_field_name(&dom_rel, new_order_1_0, ctx);
                    let dom_old_order_1_0 =
                        display_index_field_name(&dom_rel, old_order_1_0, ctx);

                    let cod_indices = index_selection
                        .indices
                        .get(&cod_rel)
                        .expect("cod rel should have indices");
                    let new_order_0_1 = cod_indices
                        .iter()
                        .filter(|index| index.age == IndexAge::New && index.order.as_ref() == [0, 1])
                        .exactly_one()
                        .expect("should have exactly one new index with order [0, 1] for cod rel");
                    let old_order_0_1 = cod_indices
                        .iter()
                        .filter(|index| index.age == IndexAge::Old && index.order.as_ref() == [0, 1])
                        .exactly_one()
                        .expect("should have exactly one old index with order [0, 1] for cod rel");

                    let cod_new_order_0_1 =
                        display_index_field_name(&cod_rel, new_order_0_1, ctx);
                    let cod_old_order_0_1 =
                        display_index_field_name(&cod_rel, old_order_0_1, ctx);

                    let set_indices = index_selection
                        .indices
                        .get(&set_rel)
                        .expect("set rel should have indices");
                    let new_order_0 = set_indices
                        .iter()
                        .filter(|index| index.age == IndexAge::New)
                        .exactly_one()
                        .expect("should have exactly one new index for set rel");
                    let old_order_0 = set_indices
                        .iter()
                        .filter(|index| index.age == IndexAge::Old)
                        .exactly_one()
                        .expect("should have exactly one old index for set rel");

                    let obj_new_order_0 = display_index_field_name(&set_rel, new_order_0, ctx);
                    let obj_old_order_0 = display_index_field_name(&set_rel, old_order_0, ctx);

                    writedoc! {f, r#"
                        let ordered_{type_snake}_mor: Vec<eqlog_runtime::MorphismWithSignature> =
                        eqlog_runtime::morphism_toposort(
                        &self.{dom_new_order_1_0},
                        &self.{dom_old_order_1_0},
                        &self.{cod_new_order_0_1},
                        &self.{cod_old_order_0_1},
                        &self.{obj_new_order_0},
                        &self.{obj_old_order_0},
                        )
                        .expect("TODO: Return error about a cycle being present in the morphism category");
                    "#}
                })
            })
            .format("\n");

        let compute_rel_sets = index_selection
            .indices
            .iter()
            .flat_map(|(rel, indices)| {
                indices
                    .iter()
                    .map(move |index| (rel.clone(), index.clone()))
            })
            .filter_map(|(flat_in_rel, index_spec)| {
                let parent_model_type = flat_in_rel.parent_model_type(ctx.signature())?;
                Some((flat_in_rel, index_spec, parent_model_type))
            })
            .map(|(flat_in_rel, index_spec, parent_model_type)| {
                FmtFn(move |f| {
                    let flat_in_rel = &flat_in_rel;
                    let flat_arity = flat_in_rel.arity(ctx.signature());
                    let arity: Vec<_> = index_spec
                        .order
                        .iter()
                        .copied()
                        .map(|i| flat_arity[i])
                        .collect();
                    let arity = arity.as_slice();

                    let index_field_name =
                        display_index_field_name(&flat_in_rel, &index_spec, ctx).to_string();
                    let index_field_name = index_field_name.as_str();

                    let columns: Vec<_> = index_spec
                        .order
                        .iter()
                        .copied()
                        .map(|column_index| {
                            morphism_index_column_kind(
                                parent_model_type,
                                column_index,
                                flat_arity[column_index],
                                ctx,
                            )
                        })
                        .collect();
                    let prefix_len = columns
                        .iter()
                        .rposition(|column| column.needs_mapping())
                        .expect("index over a parented relation should contain the parent")
                        + 1;
                    let suffix_len = arity.len() - prefix_len;
                    let prefix_columns = &columns[..prefix_len];

                    let parent_model_type_snake =
                        display_type(parent_model_type, ctx).to_string().to_case(Snake);

                    let member_maps = prefix_columns
                        .iter()
                        .copied()
                        .enumerate()
                        .filter_map(|(i, column)| match column {
                            MorphismIndexColumnKind::Member(typ) => Some(FmtFn(move |f| {
                                let map = display_mor_app_map_expr(typ, ctx, index_selection);
                                writedoc! {f, "
                                    let map_el{i} = {map};
                                "}
                            })),
                            MorphismIndexColumnKind::Parent | MorphismIndexColumnKind::Copy => None,
                        })
                        .format("\n");

                    let collect_propagated = display_morphism_index_prefix_walk(
                        prefix_columns,
                        arity.len(),
                        format!("{index_field_name}_all"),
                        true,
                    );
                    let apply_propagated = display_apply_morphism_index_propagated(
                        index_field_name,
                        arity.len(),
                        prefix_len,
                        suffix_len,
                    );
                    let suffix_type = display_prefix_tree_type(suffix_len);

                    writedoc!{f, r#"
                        let mut {index_field_name}_all = self.{index_field_name}_own.clone();
                        let {index_field_name}_own = &mut self.{index_field_name}_own;
                        #[allow(unused)]
                        for MorphismWithSignature {{ morph, dom, cod }} in ordered_{parent_model_type_snake}_mor.iter() {{
                        {member_maps}
                        let mut propagated: Vec<([u32; {prefix_len}], {suffix_type})> = Vec::new();
                        {collect_propagated}
                        {apply_propagated}
                        }}
                        self.{index_field_name}_all = {index_field_name}_all;
                    "#}
                })
            })
            .format("\n");
        writedoc! {f, "
            fn recompute_model_indices(&mut self) {{
            {compute_ordered_mor_vars}
            {compute_rel_sets}
            }}
        "}
    })
}

fn display_module_env_var<'a>(
    ram_module: &'a RamModule,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let env_struct_name = display_module_env_struct_name(ram_module);
        let in_set_fields = module_env_in_rels(ram_module)
            .into_iter()
            .map(|(flat_in_rel, index)| {
                FmtFn(move |f| {
                    let field_name = display_index_field_name(&flat_in_rel, &index, ctx);
                    if flat_in_rel.parent_model_type(ctx.signature()).is_some() {
                        write!(f, "{field_name}: &self.{field_name}_all,")
                    } else {
                        write!(f, "{field_name}: &self.{field_name},")
                    }
                })
            })
            .format("\n");

        let out_set_fields = module_env_out_rels(ram_module)
            .into_iter()
            .map(|flat_out_rel| {
                FmtFn(move |f| {
                    let field_name = display_out_set_field_name(&flat_out_rel, ctx);
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
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let module_calls = ram_modules
            .iter()
            .map(|ram_module| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let name = ram_module.name.as_str();
                    let env_var = display_module_env_var(ram_module, ctx);
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
            self.canonicalize();
            self.recompute_model_indices();
            if condition(self) {{
            return true;
            }}

            let mut delta = ModelDelta::new();


            loop {{

            {module_calls}

            self.move_new_to_old();
            delta.apply_equalities(self);
            self.canonicalize();
            delta.apply_tuples(self);
            self.recompute_model_indices();

            if condition(self) {{
            return true;
            }}

            if !self.is_dirty() {{
            delta.apply_func_defs (self);
            if !self.is_dirty() {{
            return false;
            }}
            }}
            }}
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
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        writeln!(f, "/// Creates an empty model.").unwrap();
        writeln!(f, "#[allow(dead_code)]").unwrap();
        writeln!(f, "pub fn new() -> Self {{").unwrap();
        writeln!(f, "Self {{").unwrap();
        for typ in ctx.signature().iter_types() {
            let type_snake = display_type(typ, ctx).to_string().to_case(Snake);
            writeln!(f, "{type_snake}_equalities: Unification::new(),").unwrap();
            writeln!(f, "{type_snake}_weights: Vec::new(),").unwrap();
            writeln!(f, "{type_snake}_uprooted: Vec::new(),").unwrap();
        }
        for (flat_rel, indices) in &index_selection.indices {
            for index in indices {
                let field_name = display_index_field_name(&flat_rel, &index, ctx);
                let index_type = display_index_type(&flat_rel, ctx);
                if flat_rel.parent_model_type(ctx.signature()).is_some() {
                    writeln!(f, "{field_name}_own: {index_type}::new(),").unwrap();
                    writeln!(f, "{field_name}_all: {index_type}::new(),").unwrap();
                } else {
                    writeln!(f, "{field_name}: {index_type}::new(),").unwrap();
                }
            }
        }
        for rel in iter_flat_rels(ctx.signature()) {
            let type_set: BTreeSet<TypeId> = rel.arity(ctx.signature()).into_iter().collect();
            for typ in type_set {
                let field_name = display_element_index_field_name(rel, typ, ctx);
                writeln!(f, "{field_name}: BTreeMap::new(),").unwrap();
            }
        }
        writeln!(f, "empty_join_is_dirty: true,").unwrap();
        writeln!(f, "}}").unwrap();
        write!(f, "}}").unwrap();
        Ok(())
    })
}

fn display_define_fn<'a>(func: FuncId, ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    FmtFn(move |f| {
        let func_name = display_func(func, ctx);
        let func_snake = func_name.to_string().to_case(Snake);

        let domain = flat_domain(func, ctx.signature());
        let codomain = ctx.signature().func(func).codomain;

        let codomain_camel = format!("{}", display_type(codomain, ctx)).to_case(UpperCamel);
        let codomain_snake = codomain_camel.to_case(Snake);

        let func_arg_vars: Vec<ElVar> = (0..domain.len()).map(ElVar::from).collect();
        let result_var = ElVar::from(domain.len());

        let fn_args = func_arg_vars
            .iter()
            .cloned()
            .zip(domain.iter().copied())
            .map(|(var, var_typ)| {
                FmtFn(move |f: &mut Formatter| -> Result {
                    let type_camel = format!("{}", display_type(var_typ, ctx)).to_case(UpperCamel);
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

        let codomain_parent_model = ctx.signature().type_(codomain).parents.last().copied();

        let parent_var: &str = if codomain_parent_model.is_none() {
            ""
        } else {
            "parent_el"
        };

        let define_parent_var = FmtFn(move |f| {
            let Some(model_type) = codomain_parent_model else {
                return Ok(());
            };

            let func_is_mor_app = ctx.signature().type_for_mor_app_func(func).is_some();

            if !func_is_mor_app {
                // This works if `func` is a model member function, in which case its first argument is
                // parent model. That's OK for now, but when we introduce dependent types in function
                // signatures it will break, since then the codomain might be a member type while the
                // function is not a member.
                assert_eq!(
                    ctx.signature().func(func).parents.last().copied(),
                    Some(model_type)
                );
                let parent_arg = ElVar::from(0);
                writedoc! {f, "
                    let {parent_var} = {parent_arg};"
                }?;
                return Ok(());
            }

            let cod_func = ctx
                .signature()
                .ids_for_model_type(model_type)
                .expect("parent model type should have model ids")
                .cod;
            let cod_func_snake = display_func(cod_func, ctx);

            assert!(func_is_mor_app);
            let mor_arg = ElVar::from(0);
            writedoc! {f, "
                let {parent_var} = self.define_{cod_func_snake}({mor_arg});
            "}?;
            Ok(())
        });

        writedoc! {f, "
            /// Enforces that `{func_snake}({args})` is defined, adjoining a new element if necessary.
            #[allow(dead_code)]
            pub fn define_{func_snake}(&mut self, {fn_args}) -> {codomain_camel} {{
                match self.{func_snake}({args}) {{
                    Some(result) => result,
                    None => {{
                        {define_parent_var}
                        let {result_var} = self.new_{codomain_snake}_internal({parent_var});
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
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let order = index.order.iter().format("_");
        let age = index.age;
        match rel {
            FlatInRel::Rel(rel) => {
                let rel_snake = display_rel(*rel, ctx).to_string().to_case(Snake);
                write!(f, "{rel_snake}_{age}_order_{order}")
            }
            FlatInRel::RelWithDiagonals { rel, equalities } => {
                let rel_snake = display_rel(*rel, ctx).to_string().to_case(Snake);
                let equalities = equalities.iter().format("_");
                write!(f, "{rel_snake}_{age}_eqs_{equalities}_order_{order}")
            }
            FlatInRel::TypeSet(typ) => {
                let type_snake = display_type(*typ, ctx).to_string().to_case(Snake);
                write!(f, "{type_snake}_{age}_order_0")
            }
            FlatInRel::Equality(_) => {
                panic!("Equality in relations should have been transformed the equality pass on flat eqlog")
            }
        }
    })
}

fn display_own_index_field_name<'a>(
    flat_in_rel: &'a FlatInRel,
    index: &'a IndexSpec,
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let index_field = display_index_field_name(&flat_in_rel, &index, ctx);
        if flat_in_rel.parent_model_type(ctx.signature()).is_some() {
            write!(f, "{index_field}_own")
        } else {
            write!(f, "{index_field}")
        }
    })
}

fn display_index_expr<'a>(
    flat_in_rel: &'a FlatInRel,
    index: &'a IndexSpec,
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let index_field = display_index_field_name(&flat_in_rel, &index, ctx);
        if flat_in_rel.parent_model_type(ctx.signature()).is_some() {
            write!(f, "(&self.{index_field}_all)")
        } else {
            let index_field = display_index_field_name(&flat_in_rel, &index, ctx);
            write!(f, "(&self.{index_field})")
        }
    })
}

fn display_element_index_field_name<'a>(
    rel: FlatRel,
    typ: TypeId,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let rel_snake = display_rel(rel, ctx).to_string().to_case(Snake);
        let type_snake = display_type(typ, ctx).to_string().to_case(Snake);
        write!(f, "{rel_snake}_{type_snake}_element_index")
    })
}

fn display_index_type<'a>(rel: &'a FlatInRel, ctx: &'a RustGenCtx<'a>) -> impl Display + 'a {
    FmtFn(move |f| {
        let arity_len = rel.arity(ctx.signature()).len();
        write!(f, "PrefixTree{arity_len}")
    })
}

fn display_weight_static_name<'a>(rel: FlatRel, ctx: &'a RustGenCtx<'a>) -> impl 'a + Display {
    FmtFn(move |f| {
        let rel_screaming_snake = display_rel(rel, ctx).to_string().to_case(UpperSnake);
        write!(f, "{rel_screaming_snake}_WEIGHT")
    })
}

fn display_weight_static<'a>(
    rel: FlatRel,
    index_selection: &'a IndexSelection,
    ctx: &'a RustGenCtx<'a>,
) -> impl 'a + Display {
    FmtFn(move |f| {
        let static_name = display_weight_static_name(rel, ctx);

        let el_lookup_weight = rel.arity(ctx.signature()).len();

        let relevant_indices: BTreeSet<(FlatInRel, IndexSpec)> = index_selection
            .indices
            .iter()
            .filter_map(|(flat_in_rel, index_specs)| {
                match flat_in_rel {
                    FlatInRel::Rel(rel0) => {
                        if *rel0 != rel {
                            return None;
                        }
                    }
                    FlatInRel::RelWithDiagonals {
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
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let index_fields = index_selection
            .indices
            .iter()
            .flat_map(|(rel, indices)| {
                indices
                    .iter()
                    .map(move |index| (rel.clone(), index.clone()))
            })
            .map(|(rel, index)| {
                FmtFn(move |f| {
                    let index_name = display_index_field_name(&rel, &index, ctx);
                    let index_type = display_index_type(&rel, ctx);
                    if rel.parent_model_type(ctx.signature()).is_some() {
                        writedoc! {f, "
                            {index_name}_own: {index_type},
                            {index_name}_all: {index_type},
                        "}
                    } else {
                        write!(f, "{index_name}: {index_type},")
                    }
                })
            })
            .format("\n");
        let element_index_fields = iter_flat_rels(ctx.signature())
            .map(|rel| {
                let arity: Vec<TypeId> = rel.arity(ctx.signature()).into_iter().collect();
                let arity_len = arity.len();
                let arity_set: BTreeSet<TypeId> = arity.iter().copied().collect();
                arity_set
                    .into_iter()
                    .map(move |typ| {
                        FmtFn(move |f| {
                            let field_name = display_element_index_field_name(rel, typ, ctx);
                            write!(f, "{field_name}: BTreeMap<u32, Vec<[u32; {arity_len}]>>,")
                        })
                    })
                    .format("\n")
            })
            .format("\n");

        let type_fields = ctx
            .signature()
            .iter_types()
            .map(|typ| display_type_fields(typ, ctx))
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
    ctx: &'a RustGenCtx<'a>,
    index_selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        writeln!(f, "impl {} {{", name)?;

        let new_fn = display_new_fn(ctx, index_selection);
        write!(f, "{}", new_fn)?;
        writeln!(f, "")?;

        let close_fn = display_close_fn();
        write!(f, "{}", close_fn)?;

        let close_until_fn = display_close_until_fn(ram_modules, ctx);
        write!(f, "{}", close_until_fn)?;

        for typ in ctx.signature().iter_types() {
            let iter_type_fn = display_iter_type_fn(typ, ctx, index_selection);
            write!(f, "{}", iter_type_fn)?;

            let root_fn = display_root_fn(typ, ctx);
            write!(f, "{}", root_fn)?;

            let are_equal_fn = display_are_equal_fn(typ, ctx);
            write!(f, "{}", are_equal_fn)?;

            writeln!(f, "")?;
        }

        for typ in ctx.signature().iter_types() {
            let new_element_fn_internal =
                display_new_element_fn_internal(typ, ctx, index_selection);
            writeln!(f, "{new_element_fn_internal}")?;

            let equate_elements = display_equate_elements(typ, ctx, index_selection);
            write!(f, "{}", equate_elements)?;
        }

        for typ in ctx.signature().iter_types() {
            match ctx.signature().type_(typ).kind {
                TypeKind::Plain | TypeKind::Model | TypeKind::Mor(_) => {
                    let new_el_fn = display_new_element_fn(typ, ctx);
                    writeln!(f, "{new_el_fn}")?;
                }
                TypeKind::Enum => {
                    let enum_node = ctx
                        .signature()
                        .enum_decl_for_type(typ)
                        .expect("enum type should have an enum declaration");
                    let new_enum_el_fn = display_new_enum_element(enum_node, ctx);
                    let enum_cases_fn = display_enum_cases_fn(enum_node, ctx);
                    writedoc! {f, "
                        {new_enum_el_fn}
                        {enum_cases_fn}
                    "}?;
                }
            }
        }

        for func in ctx.signature().iter_funcs() {
            let rel = FlatRel::Func(func);
            let eval_fn = display_pub_function_eval_fn(func, ctx, index_selection);
            write!(f, "{eval_fn}")?;

            let iter_fn = display_pub_iter_fn(rel, ctx, index_selection);
            write!(f, "{}", iter_fn)?;

            let insert_relation = display_pub_insert_relation(rel, ctx, index_selection, true);
            write!(f, "{}", insert_relation)?;

            writeln!(f, "")?;
        }

        for func in ctx.signature().iter_funcs() {
            if ctx.function_can_be_made_defined(func) {
                let define_fn = display_define_fn(func, ctx);
                write!(f, "{}", define_fn)?;
            }
        }

        for rel in ctx.pred_like_rels() {
            let arity = rel.arity(ctx.signature());
            let arity: Vec<String> = arity
                .into_iter()
                .map(|typ| display_type(typ, ctx).to_string())
                .collect();
            let arity: Vec<&str> = arity.iter().map(|s| s.as_str()).collect();

            let predicate_holds_fn = display_pub_predicate_holds_fn(rel, ctx, index_selection);
            write!(f, "{}", predicate_holds_fn)?;

            if !arity.is_empty() {
                let iter_fn = display_pub_iter_fn(rel, ctx, index_selection);
                write!(f, "{}", iter_fn)?;
            }

            let insert_relation = display_pub_insert_relation(rel, ctx, index_selection, false);
            write!(f, "{}", insert_relation)?;

            writeln!(f, "")?;
        }

        let canonicalize_fn = display_canonicalize_fn(ctx, index_selection);
        write!(f, "{canonicalize_fn}\n")?;

        let is_dirty_fn = display_is_dirty_fn(ctx, index_selection);
        write!(f, "{}", is_dirty_fn)?;

        writeln!(f, "")?;

        let recompute_model_indices_fn = display_recompute_model_indices_fn(ctx, index_selection);
        write!(f, "{}", recompute_model_indices_fn)?;

        let move_new_to_old_fn = display_move_new_to_old_fn(ctx, index_selection);
        write!(f, "{move_new_to_old_fn}")?;

        write!(f, "}}")?;
        Ok(())
    })
}

fn display_rule_modules<'a>(
    ram_modules: &'a [RamModule],
    index_selection: &'a IndexSelection,
    ctx: &'a RustGenCtx<'a>,
    symbol_prefix: &'a str,
) -> impl 'a + Display {
    ram_modules
        .iter()
        .map(move |ram_module| {
            FmtFn(move |f| {
                let lib = display_ram_module(ram_module, index_selection, ctx, symbol_prefix);
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
    ctx: &'a RustGenCtx<'a>,
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
                display_rule_modules(ram_modules, index_selection, ctx, symbol_prefix).fmt(f)?;
            }
        }

        let module_env_structs = ram_modules
            .iter()
            .map(|ram_module| display_module_env_struct(ram_module, ctx))
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

        for rel in iter_flat_rels(ctx.signature()) {
            let weight_static = display_weight_static(rel, index_selection, ctx);
            write!(f, "{weight_static}")?;
        }

        for typ in ctx.signature().iter_types() {
            let type_struct = display_type_struct(typ, ctx);
            write!(f, "{}", type_struct)?;
            let type_impl = display_type_impl(typ, ctx);
            write!(f, "{}", type_impl)?;
        }
        write!(f, "\n")?;

        for (enum_decl, _) in ctx.signature().iter_enum_decls() {
            writeln!(f, "{}", display_enum(enum_decl, ctx))?;
        }

        for func in ctx.signature().iter_funcs() {
            let func_args_struct = display_func_args_struct(func, ctx);
            writeln!(f, "{func_args_struct}")?;
        }

        write!(f, "\n")?;

        let model_delta_struct = display_model_delta_struct(ctx);
        write!(f, "{}", model_delta_struct)?;

        let theory_struct = display_theory_struct(name, ctx, index_selection);
        write!(f, "{}", theory_struct)?;

        let model_delta_impl = display_model_delta_impl(ctx);
        write!(f, "{}", model_delta_impl)?;
        write!(f, "\n")?;

        let theory_impl = display_theory_impl(name, ram_modules, ctx, index_selection);
        write!(f, "{}", theory_impl)?;

        Ok(())
    })
}
