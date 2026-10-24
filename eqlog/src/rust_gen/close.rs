use indoc::writedoc;

use crate::ram::CloseOperation;

pub(super) fn emit_operation(
    f: &mut std::fmt::Formatter<'_>,
    operation: &CloseOperation,
) -> std::fmt::Result {
    let source = match operation {
        CloseOperation::CanonicalizeRelations => "self.__canonicalize_relations();",
        CloseOperation::TakeDelta => {
            "let mut delta = std::mem::replace(&mut self.__pending_delta, ModelDelta::new());"
        }
        CloseOperation::ClearAllocated => "self.__allocated = false;",
        CloseOperation::ApplyDeferredFunctions => "delta.apply_func_defs(self);",
        CloseOperation::SaveDelta => "std::mem::swap(&mut self.__pending_delta, &mut delta);",
        CloseOperation::Canonicalize => "self.canonicalize();",
        CloseOperation::MarkClosed => "self.__closed = true;",
        CloseOperation::ReturnFalse => "return false;",
        CloseOperation::ReturnCondition => {
            "return condition.is_some_and(|condition| condition(self));"
        }
        CloseOperation::CheckConditionBeforeDelta => {
            "if self.__check_condition(condition) { return true; }"
        }
        CloseOperation::CheckCondition => {
            // Moving the delta at each exit grows debug stack frames with the number of strata.
            return writedoc! {f, "
                if self.__check_condition(condition) {{
                    std::mem::swap(&mut self.__pending_delta, &mut delta);
                    return true;
                }}
            "};
        }
        CloseOperation::InitializeChanges(id) => {
            return writeln!(f, "let mut active_{id} = false;");
        }
        CloseOperation::MarkChanged(id) => return writeln!(f, "active_{id} = true;"),
        CloseOperation::BreakUnlessChanged(id) => {
            return writeln!(f, "if !active_{id} {{ break; }}");
        }
    };
    writeln!(f, "{source}")
}
