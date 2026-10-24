use super::RustGenCtx;
use crate::ram::CompactRejection;

pub(super) fn rejection_message(reason: &CompactRejection, ctx: &RustGenCtx<'_>) -> String {
    match reason {
        CompactRejection::NativeRequired => "compact members require native evaluation".into(),
        CompactRejection::NotModel(model) => {
            let model_name = ctx.type_name(*model);
            format!("{model_name} is not a model type")
        }
        CompactRejection::EnclosingCoordinates(model) => {
            let model_name = ctx.type_name(*model);
            format!("{model_name} has enclosing model coordinates")
        }
        CompactRejection::UnsupportedMember { model, member } => {
            let model_name = ctx.type_name(*model);
            let name = ctx.type_name(*member);
            format!("{model_name} has unsupported nested or non-plain member {name}")
        }
        CompactRejection::NoMembers(model) => {
            let model_name = ctx.type_name(*model);
            format!("{model_name} has no direct plain members")
        }
        CompactRejection::ForeignColumn { rel, column } => {
            let name = ctx.rel_name(*rel);
            format!("{name} column {column} uses foreign or dependent member coordinates")
        }
        CompactRejection::OutsideOwner { rel, model } => {
            let name = ctx.rel_name(*rel);
            let model_name = ctx.type_name(*model);
            format!("{name} stores {model_name} members outside their owner")
        }
        CompactRejection::IncompleteIndex(rel) => {
            let name = ctx.rel_name(*rel);
            format!("{name} has an incomplete compact index projection")
        }
        CompactRejection::NonleadingIndex(rel) => {
            let name = ctx.rel_name(*rel);
            format!("{name} has a member index without a leading owner")
        }
        CompactRejection::DiagonalIndex(rel) => {
            let name = ctx.rel_name(*rel);
            format!("{name} has an unsupported member-bearing diagonal index")
        }
        CompactRejection::RuleScope { name, model } => {
            let model_name = ctx.type_name(*model);
            format!("rule {name} uses members outside one {model_name} scope")
        }
        CompactRejection::ExecutionScope(name) => {
            format!("rule {name} executes outside its compact owner scope")
        }
        CompactRejection::ReadScope(name) => {
            format!("rule {name} reads members through an unsupported or different owner coordinate space")
        }
        CompactRejection::WriteScope(name) => {
            format!("rule {name} writes members outside its compact owner coordinate space")
        }
        CompactRejection::InputIndex(name) => {
            format!("rule {name} selects an unsupported compact member input index")
        }
    }
}
