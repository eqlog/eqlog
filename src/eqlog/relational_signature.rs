use std::fmt::Debug;
use super::enumerable::*;
use std::marker::PhantomData;

pub trait RelationalSignature {
    type Sort: 'static + Into<usize> + Copy + PartialEq + Eq + Debug;
    type Relation: 'static + Into<usize> + Copy + PartialEq + Eq + Debug;

    fn sorts(&self) -> &[Self::Sort];
    fn relations(&self) -> &[Self::Relation];
    fn arity(&self, relation: Self::Relation) -> &[Self::Sort];
}

pub trait StaticArity<S> {
    fn arity(self) -> &'static [S];
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

impl<S: PartialEq + Eq + Debug, R: PartialEq + Eq + Debug>
RelationalSignature for StaticSignature<S, R>
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

#[macro_export]
macro_rules! relational_arities {
    (
        pub enum $sort_type:ident $sorts:tt,
        pub enum $relation_type:ident {
            $($relation:ident : $($arg_sort:ident)x*),* $(,)?
        },
    ) => {
        enumerable_type!(pub enum $sort_type $sorts);
        enumerable_type!(pub enum $relation_type { $($relation),* });
        impl $crate::eqlog::relational_signature::StaticArity<$sort_type> for $relation_type {
            fn arity(self) -> &'static [$sort_type] {
                match self {
                    $($relation_type::$relation => {
                        &[$($sort_type::$arg_sort),*]
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
        relational_arities!{
            pub enum Sort {S0, S1},
            pub enum Relation {
                R0: S0 x S1,
                R1: ,
                R2: S1 x S0,
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
            s.arity(R1),
            &[],
        );

        assert_eq!(
            s.arity(R2),
            &[S1, S0],
        );

        assert_eq!(
            s.arity(R3),
            &[S0, S0],
        );
    }
}
