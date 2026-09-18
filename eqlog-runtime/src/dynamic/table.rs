use crate::wbtree::map::WBTreeMap;
use crate::{
    PrefixTree0, PrefixTree1, PrefixTree2, PrefixTree3, PrefixTree4, PrefixTree5, PrefixTree6,
    PrefixTree7, PrefixTree8, PrefixTree9,
};

// Reuse compiled storage for fixed arities; extend its layout for larger tuples.
macro_rules! table {
    ($($variant:ident($tree:ident, $arity:literal)),* $(,)?) => {
        #[derive(Clone, Debug)]
        pub(super) enum Table {
            $($variant($tree),)*
            Long { arity: usize, rows: WBTreeMap<Table> },
        }

        impl Table {
            pub(super) fn new(arity: usize) -> Self {
                match arity {
                    $($arity => Self::$variant($tree::new()),)*
                    arity => Self::Long { arity, rows: WBTreeMap::new() },
                }
            }

            pub(super) fn insert(&mut self, tuple: &[u32]) -> bool {
                match self {
                    $(Self::$variant(tree) => tree.insert(tuple.try_into().expect("validated tuple arity")),)*
                    Self::Long { arity, rows } => {
                        assert_eq!(tuple.len(), *arity);
                        rows.entry(tuple[0]).or_insert_with(|| Self::new(*arity - 1)).insert(&tuple[1..])
                    }
                }
            }

            pub(super) fn contains(&self, tuple: &[u32]) -> bool {
                match self {
                    $(Self::$variant(tree) => tree.contains(tuple.try_into().expect("validated tuple arity")),)*
                    Self::Long { arity, rows } => {
                        assert_eq!(tuple.len(), *arity);
                        rows.get(&tuple[0]).is_some_and(|tree| tree.contains(&tuple[1..]))
                    }
                }
            }

            pub(super) fn iter(&self) -> Box<dyn Iterator<Item = Vec<u32>> + '_> {
                match self {
                    $(Self::$variant(tree) => Box::new(tree.iter().map(Vec::from)),)*
                    Self::Long { arity: _, rows } => Box::new(rows.iter().flat_map(|(first, tree)| {
                        tree.iter().map(move |mut tuple| {
                            tuple.insert(0, first);
                            tuple
                        })
                    })),
                }
            }
        }
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
