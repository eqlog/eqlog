//! Generated models need cross-crate access to the runtime's storage.

use std::sync::Arc;

pub use super::data::{RelationData, RelationIndex, SortData};
pub use super::table::Table;
use super::{DynamicModel, Error, RelationId, Signature, SortId};

pub fn from_parts(
    signature: Arc<Signature>,
    sorts: Vec<SortData>,
    relations: Vec<RelationData>,
) -> Result<DynamicModel, Error> {
    DynamicModel::from_parts(signature, sorts, relations)
}

pub fn sort_data(model: &DynamicModel, sort: SortId) -> Result<&SortData, Error> {
    model.sort_data(sort)
}

pub fn relation_data(model: &DynamicModel, relation: RelationId) -> Result<&RelationData, Error> {
    model.relation_data(relation)
}
