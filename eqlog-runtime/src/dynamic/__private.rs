//! Generated models need cross-crate access to the runtime's storage.

use std::sync::Arc;

pub use super::data::{RelationData, RelationIndex, TypeData};
pub use super::table::Table;
use super::{DynamicModel, Error, RelationId, Signature, TypeId};

pub fn from_parts(
    signature: Arc<Signature>,
    types: Vec<TypeData>,
    relations: Vec<RelationData>,
) -> Result<DynamicModel, Error> {
    DynamicModel::from_parts(signature, types, relations)
}

pub fn type_data(model: &DynamicModel, type_: TypeId) -> Result<&TypeData, Error> {
    model.type_data(type_)
}

pub fn relation_data(model: &DynamicModel, relation: RelationId) -> Result<&RelationData, Error> {
    model.relation_data(relation)
}
