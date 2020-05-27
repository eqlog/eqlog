pub trait Enumerable: Sized + Copy + Into<usize> + 'static {
    const VALUES: &'static [Self];
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
        impl $crate::eqlog::enumerable::Enumerable for $type {
            const VALUES: &'static [$type] = &[$($type::$variant),*];
        }
        impl std::fmt::Display for $type {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
                std::fmt::Debug::fmt(self, f)
            }
        }
    }
}
