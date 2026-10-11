use std::fmt::Display;

use indoc::writedoc;
use itertools::Itertools;

use super::{
    display_all_index_field_name, display_index_type, display_own_index_field_name, RustGenCtx,
};
use crate::flat_eqlog::{FlatInRel, FlatRel, IndexSelection, IndexSpec};
use crate::fmt_util::FmtFn;

pub(super) fn source_relation(rel: &FlatInRel) -> FlatInRel {
    match rel {
        FlatInRel::RelWithDiagonals { rel, .. } => FlatInRel::Rel(*rel),
        FlatInRel::Rel(_) | FlatInRel::TypeSet(_) => rel.clone(),
        FlatInRel::Equality(_) => unreachable!("equalities have no tuple indices"),
    }
}

pub(super) fn read_method(
    rel: &FlatInRel,
    index: &IndexSpec,
    indices: &IndexSelection,
    ctx: &RustGenCtx<'_>,
    prepared: bool,
) -> String {
    let field = display_all_index_field_name(rel, index, ctx);
    if prepared && !indices.is_primary(rel, index) {
        format!("{field}.prepared")
    } else {
        field.to_string()
    }
}

pub(super) fn prepare<'a>(
    rel: &'a FlatInRel,
    index: &'a IndexSpec,
    indices: &'a IndexSelection,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        if indices.is_primary(rel, index) {
            return Ok(());
        }
        let source = source_relation(rel);
        let primary = indices.current_primary(&source);
        let source_field = display_all_index_field_name(&source, primary, ctx);
        let field = display_all_index_field_name(rel, index, ctx);
        let project = projection(rel, index, primary);
        writeln!(f, "self.{field}.prepare(&self.{source_field}, {project});")
    })
}

pub(super) fn projection(rel: &FlatInRel, index: &IndexSpec, source: &IndexSpec) -> String {
    let columns: Vec<_> = match rel {
        FlatInRel::RelWithDiagonals { equalities, .. } => equalities
            .iter()
            .enumerate()
            .filter_map(|(i, &j)| (i == j).then_some(i))
            .collect(),
        FlatInRel::Rel(_) | FlatInRel::TypeSet(_) => (0..source.order.len()).collect(),
        FlatInRel::Equality(_) => unreachable!("equalities have no tuple indices"),
    };
    let row = source.order.iter().map(|i| format!("el{i}")).join(", ");
    let result = index
        .order
        .iter()
        .map(|&i| {
            let column = columns[i];
            format!("el{column}")
        })
        .join(", ");
    let checks = match rel {
        FlatInRel::RelWithDiagonals { equalities, .. } => equalities
            .iter()
            .enumerate()
            .filter(|&(i, j)| i != *j)
            .map(|(i, j)| format!("el{i} == el{j}"))
            .join(" && "),
        FlatInRel::Rel(_) | FlatInRel::TypeSet(_) => String::new(),
        FlatInRel::Equality(_) => unreachable!("equalities have no tuple indices"),
    };
    if checks.is_empty() {
        format!("|[{row}]| Some([{result}])")
    } else {
        format!("|[{row}]| ({checks}).then_some([{result}])")
    }
}

pub(super) fn field_type<'a>(
    rel: &'a FlatInRel,
    index: &'a IndexSpec,
    indices: &'a IndexSelection,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        let target = display_index_type(rel, ctx);
        if indices.is_primary(rel, index) {
            write!(f, "{target}")
        } else {
            let source = source_relation(rel);
            let source_type = display_index_type(&source, ctx);
            write!(
                f,
                "eqlog_runtime::__private::LazyIndex<{source_type}, {target}>"
            )
        }
    })
}

pub(super) fn accessors<'a>(
    indices: &'a IndexSelection,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        for (rel, index) in indices.current_indices() {
            let typ = display_index_type(rel, ctx);
            let source = source_relation(rel);
            let primary = indices.current_primary(&source);
            let project = projection(rel, index, primary);
            let mut fields = vec![(
                display_all_index_field_name(rel, index, ctx).to_string(),
                display_all_index_field_name(&source, primary, ctx).to_string(),
            )];
            if ctx.has_shared_indices(rel) && indices.is_primary(rel, index) {
                fields.push((
                    display_own_index_field_name(rel, index, ctx).to_string(),
                    display_own_index_field_name(&source, primary, ctx).to_string(),
                ));
            }
            for (field, source) in fields {
                let expr = if indices.is_primary(rel, index) {
                    format!("&self.{field}")
                } else {
                    format!("self.{field}.get(&self.{source}, {project})")
                };
                writedoc! {f, "
                        #[allow(dead_code)]
                        fn {field}(&self) -> &{typ} {{ {expr} }}
                    "}?;
            }
        }
        Ok(())
    })
}

pub(super) fn invalidate<'a>(
    relation: FlatRel,
    indices: &'a IndexSelection,
    ctx: &'a RustGenCtx<'a>,
) -> impl Display + 'a {
    FmtFn(move |f| {
        for (rel, specs) in &indices.indices {
            if source_relation(rel) != FlatInRel::Rel(relation) {
                continue;
            }
            for index in specs
                .iter()
                .unique_by(|index| &index.order)
                .filter(|index| !indices.is_primary(rel, index))
            {
                let all = display_all_index_field_name(rel, index, ctx);
                writeln!(f, "self.{all}.invalidate();")?;
            }
        }
        Ok(())
    })
}
