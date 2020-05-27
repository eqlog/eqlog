pub use super::signature::*;
pub use super::syntax::*;
pub use super::closure::*;
use std::fmt::Display;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Theory<Sig: Signature> {
    pub signature: Sig,
    pub functionalities: Vec<(Sig::Relation, SurjectionPresentation<Sig>)>,
    pub axioms: Vec<(Sequent, SurjectionPresentation<Sig>)>,
}

impl<Sig: Signature + Copy> Theory<Sig>
where
    <Sig as RelationalSignature>::Sort: Display,
    <Sig as RelationalSignature>::Relation: Display,
{
    pub fn new(sig: Sig, axioms: impl IntoIterator<Item = Sequent>) -> Self {
        Theory {
            signature: sig,
            functionalities: 
                sig.relations().iter()
                .copied()
                .filter(|&r| sig.relation_kind(r) == RelationKind::Operation)
                .map(|op| (op, SurjectionPresentation::functionality(&sig, op)))
                .collect(),
            axioms:
                axioms.into_iter()
                .map(|sequent| {
                    let csp = to_surjection_presentation(&sig, &sequent);
                    (sequent, csp)
                })
                .collect(),
        }
    }
}
