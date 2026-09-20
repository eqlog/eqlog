use super::Error;
use crate::wbtree::map::WBTreeMap;
use crate::{
    PrefixTree0, PrefixTree1, PrefixTree2, PrefixTree3, PrefixTree4, PrefixTree5, PrefixTree6,
    PrefixTree7, PrefixTree8, PrefixTree9,
};

/// A prefix tree whose arity is known at runtime.
/// Cloning shares tree nodes until either copy is modified.
#[derive(Clone, Debug)]
pub struct Table(Rows);

macro_rules! conversions {
    ([$($previous:ident,)*];) => {};
    ([$($previous:ident,)*]; $variant:ident($tree:ident, $arity:literal), $($next:ident($next_tree:ident, $next_arity:literal),)*) => {
        impl From<$tree> for Table {
            fn from(tree: $tree) -> Self { Self(Rows::$variant(tree)) }
        }

        impl TryFrom<&Table> for $tree {
            type Error = Error;

            fn try_from(table: &Table) -> Result<Self, Error> {
                match &table.0 {
                    Rows::$variant(tree) => Ok(tree.clone()),
                    $(Rows::$previous(_) |)* $(Rows::$next(_) |)* Rows::Long { .. } => {
                        Err(Error::ArityMismatch { expected: $arity, actual: table.arity() })
                    }
                }
            }
        }

        conversions!([$($previous,)* $variant,]; $($next($next_tree, $next_arity),)*);
    };
}

macro_rules! table {
    ($($variant:ident($tree:ident, $arity:literal)),* $(,)?) => {
        #[derive(Clone, Debug)]
        enum Rows {
            $($variant($tree),)*
            Long { arity: usize, rows: WBTreeMap<Table> },
        }

        impl Table {
            /// Creates an empty table.
            pub fn new(arity: usize) -> Self {
                Self(match arity {
                    $($arity => Rows::$variant($tree::new()),)*
                    arity => Rows::Long { arity, rows: WBTreeMap::new() },
                })
            }

            pub fn arity(&self) -> usize {
                match &self.0 {
                    $(Rows::$variant(_) => $arity,)*
                    Rows::Long { arity, rows: _ } => *arity,
                }
            }

            /// Inserts a row. Panics if its length differs from the table's arity.
            pub fn insert(&mut self, tuple: &[u32]) -> bool {
                match &mut self.0 {
                    $(Rows::$variant(tree) => tree.insert(tuple.try_into().expect("tuple arity")),)*
                    Rows::Long { arity, rows } => {
                        assert_eq!(tuple.len(), *arity);
                        rows.entry(tuple[0]).or_insert_with(|| Self::new(*arity - 1)).insert(&tuple[1..])
                    }
                }
            }

            /// Checks for an exact row. Panics if its length differs from the arity.
            pub fn contains(&self, tuple: &[u32]) -> bool {
                match &self.0 {
                    $(Rows::$variant(tree) => tree.contains(tuple.try_into().expect("tuple arity")),)*
                    Rows::Long { arity, rows } => {
                        assert_eq!(tuple.len(), *arity);
                        rows.get(&tuple[0]).is_some_and(|tree| tree.contains(&tuple[1..]))
                    }
                }
            }

            pub fn iter(&self) -> Box<dyn Iterator<Item = Vec<u32>> + '_> {
                match &self.0 {
                    $(Rows::$variant(tree) => Box::new(tree.iter().map(Vec::from)),)*
                    Rows::Long { arity: _, rows } => Box::new(rows.iter().flat_map(|(first, tree)| {
                        tree.iter().map(move |mut tuple| {
                            tuple.insert(0, first);
                            tuple
                        })
                    })),
                }
            }

            /// Unites tables of the same arity, sharing unchanged subtrees.
            pub fn union(&self, other: &Self) -> Self {
                assert_eq!(self.arity(), other.arity());
                Self(match &self.0 {
                    $(Rows::$variant(tree) => {
                        let other = $tree::try_from(other).expect("equal arities");
                        Rows::$variant(tree.union(&other))
                    },)*
                    Rows::Long { arity, rows } => {
                        let other_rows = match &other.0 {
                            $(Rows::$variant(_) => unreachable!("equal arities"),)*
                            Rows::Long { arity: _, rows } => rows,
                        };
                        Rows::Long {
                            arity: *arity,
                            rows: rows.union(other_rows, |_, left, right| left.union(&right)),
                        }
                    }
                })
            }
        }

        conversions!([]; $($variant($tree, $arity),)*);
    };
}

table! {
    Rows0(PrefixTree0, 0),
    Rows1(PrefixTree1, 1),
    Rows2(PrefixTree2, 2),
    Rows3(PrefixTree3, 3),
    Rows4(PrefixTree4, 4),
    Rows5(PrefixTree5, 5),
    Rows6(PrefixTree6, 6),
    Rows7(PrefixTree7, 7),
    Rows8(PrefixTree8, 8),
    Rows9(PrefixTree9, 9),
}
