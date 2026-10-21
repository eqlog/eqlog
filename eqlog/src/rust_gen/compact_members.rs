use convert_case::{Case, Casing};
use indoc::writedoc;
use std::fmt::Display;

use super::{
    display_current_index_field_name, display_element_index_field_name, display_type, RustGenCtx,
};
use crate::algebra::signature::TypeId;
use crate::flat_eqlog::{FlatInRel, FlatRel, IndexSelection};
use crate::fmt_util::FmtFn;

pub(super) fn methods<'a>(
    typ: TypeId,
    ctx: &'a RustGenCtx<'a>,
    selection: &'a IndexSelection,
) -> impl Display + 'a {
    FmtFn(move |f| {
        if !ctx.supports_compact_members(typ) {
            return Ok(());
        }
        let camel = display_type(typ, ctx).to_string().to_case(Case::UpperCamel);
        let name = camel.to_case(Case::Snake);
        let parent = ctx.signature().type_(typ).parents[0];
        let parent_camel = display_type(parent, ctx)
            .to_string()
            .to_case(Case::UpperCamel);
        let parent_name = parent_camel.to_case(Case::Snake);
        let membership = display_element_index_field_name(FlatRel::ModelMember(typ), typ, ctx);
        let type_set = FlatInRel::TypeSet(typ);
        let elements =
            display_current_index_field_name(&type_set, selection.current_primary(&type_set), ctx);
        writedoc! {f, "
            fn __enable_compact_{name}(&mut self) {{
                if self.__compact_members_{name}.is_some() {{ return; }}
                let bound = self.{name}_equalities.len();
                let mut spaces = eqlog_runtime::__private::MemberSpaces::with_handle_bound(bound as u64);
                for owner in self.iter_{parent_name}() {{ spaces.create_owner(owner.0); }}
                for id in 0..bound {{
                    let member = {camel}(u32::try_from(id).unwrap());
                    let root = self.{name}_equalities.root_const(member);
                    if !self.{elements}.contains([root.0]) {{ continue; }}
                    let rows = self.{membership}.get(&root.0)
                        .expect(\"a member representative has an enclosing model\");
                    let owner = self.root_{parent_name}({parent_camel}(rows[0][0])).0;
                    assert!(rows.iter().all(|row| self.root_{parent_name}({parent_camel}(row[0])).0 == owner),
                        \"compact members require a unique enclosing model\");
                    spaces.adopt(owner, member.0);
                }}
                for id in 0..bound {{
                    let member = {camel}(u32::try_from(id).unwrap());
                    if let Some(owner) = spaces.owner(member.0) {{
                        let root = self.{name}_equalities.root_const(member);
                        spaces.equate(owner, member.0, root.0);
                        self.{name}_uprooted.push(member);
                    }}
                }}
                self.__compact_members_{name} = Some(spaces);
                self.__sync_compact_{name}_weights();
                self.__closed = false;
            }}

            fn __sync_compact_{name}_weights(&mut self) {{
                if let Some(spaces) = &self.__compact_members_{name} {{
                    self.{name}_weights.increase_size_to(usize::try_from(spaces.handle_bound()).unwrap());
                }}
            }}

            fn __compact_{name}_origin(&self, owner: u32, member: {camel}) -> u32 {{
                match &self.__compact_members_{name} {{
                    Some(spaces) => spaces.get_snapshot(owner)
                        .and_then(|snapshot| snapshot.origin(member.0))
                        .expect(\"member belongs to the enclosing compact model\"),
                    None => member.0,
                }}
            }}

            fn __compact_{name}_uid(&self, owner: u32, origin: u32) -> {camel} {{
                match &self.__compact_members_{name} {{
                    Some(spaces) => {camel}(spaces.get_snapshot(owner)
                        .and_then(|snapshot| snapshot.handle(origin))
                        .expect(\"origin belongs to the enclosing compact model\")),
                    None => {camel}(origin),
                }}
            }}

            fn __compact_{name}_snapshot(&self, owner: u32) -> Option<&eqlog_runtime::__private::MemberSnapshot> {{
                self.__compact_members_{name}.as_ref().and_then(|spaces| spaces.get_snapshot(owner))
            }}
        "}
    })
}
