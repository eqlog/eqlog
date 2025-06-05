#[doc(hidden)]
pub mod btree_set;
mod types;
#[doc(hidden)]
pub mod unification;

/// Declare an eqlog module.
///
/// # Examples
///
/// ```ignore
/// use eqlog_runtime::eqlog_mod;
/// eqlog_mod!(foo);
/// ```
///
/// Eqlog modules can be annotated with a visibility, or with attributes:
/// ```ignore
/// eqlog_mod!(#[cfg(test)] pub foo);
/// ```
#[macro_export]
macro_rules! eqlog_mod {
    ($(#[$attr:meta])* $vis:vis $modname:ident) => {
        $(#[$attr])* $vis mod $modname {
            include!(concat!(
                env!("EQLOG_OUT_DIR"),
                "/",
                file!(),
                "/",
                "..",
                "/",
                stringify!($modname),
                ".eql.rs"
            ));
        }
    };
}
