use std::fmt::Debug;
use super::enumerable::*;
pub use super::relational_signature::*;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum RelationKind {
    Predicate,
    Operation,
}

pub trait Signature: RelationalSignature {
    fn relation_kind(&self, r: Self::Relation) -> RelationKind;
}

pub trait StaticRelationKind {
    fn relation_kind(&self) -> RelationKind;
}

impl<S, R> Signature for StaticSignature<S, R>
where
    S: Enumerable + PartialEq + Eq + Debug,
    R: Enumerable + StaticArity<S> + StaticRelationKind + PartialEq + Eq + Debug,
{
    fn relation_kind(&self, r: R) -> RelationKind {
        r.relation_kind()
    }
}

#[macro_export]
macro_rules! arities {
    (
        pub enum $sort_type:ident $sorts:tt,
        pub enum $relation_type:ident {
            $($relation:ident : $($arg_sort:ident)x* $(-> $cod:ident)?),* $(,)?
        },
    ) => {
        enumerable_type!(pub enum $sort_type $sorts);
        enumerable_type!(pub enum $relation_type { $($relation),* });
        impl $crate::eqlog::relational_signature::StaticArity<$sort_type> for $relation_type {
            fn arity(self) -> &'static [$sort_type] {
                match self {
                    $($relation_type::$relation => {
                        &[$($sort_type::$arg_sort),* $(, $sort_type::$cod)?]
                    }),*
                }
            }
        }

        impl $crate::eqlog::signature::StaticRelationKind for $relation_type {
            #[allow(unreachable_code)]
            fn relation_kind(&self) -> $crate::eqlog::signature::RelationKind {
                match self {
                    $($relation_type::$relation => {
                        $(let _ = $sort_type::$cod; return $crate::eqlog::signature::RelationKind::Operation;)?
                        return $crate::eqlog::signature::RelationKind::Predicate;
                    }),*
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn arities() {
        arities!{
            pub enum Sort {S0, S1},
            pub enum Relation {
                R0: S0 x S1,
                R1: ,
                R2: S1 x S0 -> S1,
                R3: S0 x S0,
            },
        }
        pub use Sort::*;
        pub use Relation::*;
        pub type Sig = StaticSignature<Sort, Relation>;

        let s = Sig::new();
        assert_eq!(
            s.sorts(),
            &[S0, S1],
        );
        assert_eq!(
            s.relations(),
            &[R0, R1, R2, R3],
        );

        assert_eq!(
            s.arity(R0),
            &[S0, S1],
        );
        assert_eq!(
            R0.relation_kind(),
            RelationKind::Predicate,
        );

        assert_eq!(
            s.arity(R1),
            &[],
        );
        assert_eq!(
            R1.relation_kind(),
            RelationKind::Predicate,
        );

        assert_eq!(
            s.arity(R2),
            &[S1, S0, S1],
        );
        assert_eq!(
            R2.relation_kind(),
            RelationKind::Operation,
        );

        assert_eq!(
            s.arity(R3),
            &[S0, S0],
        );
        assert_eq!(
            R3.relation_kind(),
            RelationKind::Predicate,
        );
    }
}
