use std::marker::{PhantomData, Sized};
use std::fmt::Debug;

pub trait Signature {
    type Sort: 'static + Into<usize> + Copy + PartialEq + Eq + Debug;
    type Relation: 'static + Into<usize> + Copy + PartialEq + Eq + Debug;

    fn sorts(&self) -> &[Self::Sort];
    fn relations(&self) -> &[Self::Relation];
    fn arity(&self, relation: Self::Relation) -> &[Self::Sort];
}

impl<'a, S: Signature> Signature for &'a S {
    type Sort = S::Sort;
    type Relation = S::Relation;

    fn sorts(&self) -> &[Self::Sort] {
        (*self).sorts()
    }
    fn relations(&self) -> &[Self::Relation] {
        (*self).relations()
    }
    fn arity(&self, relation: Self::Relation) -> &[Self::Sort] {
        (*self).arity(relation)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct StaticSignature<S, R> {
    sort: PhantomData<S>,
    relation: PhantomData<R>,
}

impl<S, R> StaticSignature<S, R> {
    pub fn new() -> Self {
        StaticSignature {
            sort: PhantomData,
            relation: PhantomData,
        }
    }
}

pub trait Enumerable: Sized + Copy + Into<usize> + 'static {
    const VALUES: &'static [Self];
}

pub trait StaticArity<S> {
    fn arity(self) -> &'static [S];
}

impl<S: PartialEq + Eq + Debug, R: PartialEq + Eq + Debug> Signature for StaticSignature<S, R>
where
    S: Enumerable,
    R: Enumerable + StaticArity<S>,
{
    type Sort = S;
    type Relation = R;

    fn sorts(&self) -> &[Self::Sort] {
        Self::Sort::VALUES
    }
    fn relations(&self) -> &[Self::Relation] {
        Self::Relation::VALUES
    }
    fn arity(&self, relation: Self::Relation) -> &[Self::Sort] {
        relation.arity()
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum RelationKind {
    Predicate,
    Operation,
}

pub trait PredicateOrOperation {
    fn kind(self) -> RelationKind;
}

#[macro_export]
macro_rules! enumerable_type {
    (pub enum $type:ident { $($variant:ident),* $(,)?}) => {
        #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
        pub enum $type {
            $($variant),*
        }
        impl Into<usize> for $type {
            fn into(self) -> usize {
                self as usize
            }
        }
        impl $crate::eqlog::signature::Enumerable for $type {
            const VALUES: &'static [$type] = &[$($type::$variant),*];
        }
        impl std::fmt::Display for $type {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
                std::fmt::Debug::fmt(self, f)
            }
        }
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
        impl $crate::eqlog::signature::StaticArity<$sort_type> for $relation_type {
            fn arity(self) -> &'static [$sort_type] {
                match self {
                    $($relation_type::$relation => {
                        &[$($sort_type::$arg_sort),* $(, $sort_type::$cod)?]
                    }),*
                }
            }
        }

        impl $crate::eqlog::signature::PredicateOrOperation for $relation_type {
            #[allow(unreachable_code)]
            fn kind(self) -> $crate::eqlog::signature::RelationKind {
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

        let s0 = Sig::new();
        let s = &s0;
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
            R0.kind(),
            RelationKind::Predicate,
        );

        assert_eq!(
            s.arity(R1),
            &[],
        );
        assert_eq!(
            R1.kind(),
            RelationKind::Predicate,
        );

        assert_eq!(
            s.arity(R2),
            &[S1, S0, S1],
        );
        assert_eq!(
            R2.kind(),
            RelationKind::Operation,
        );

        assert_eq!(
            s.arity(R3),
            &[S0, S0],
        );
        assert_eq!(
            R3.kind(),
            RelationKind::Predicate,
        );
    }
}
