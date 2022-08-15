mod unification;

#[doc(hidden)]
pub use crate::unification::Unification;
#[doc(hidden)]
pub extern crate rayon;
#[doc(hidden)]
pub extern crate tabled;

/// Declare an eqlog module.
///
/// # Examples
/// The following simple version declares a module `foo` whose contents correspond `src/foo.eqlog`.
/// ```ignore
/// use eqlog_runtime::eqlog_mod;
/// eqlog_mod!(foo);
/// ```
///
/// This variant does not work for eqlog in proper subdirectories of `src`.
/// For example, it will not work for `src/bar/baz.eqlog`.
/// For such eqlog files, the following invocation of the `eqlog_mod` macro must be used:
/// ```ignore
/// eqlog_mod!(baz, "/bar/baz.rs")
/// ```
/// This declares a submodule `baz` in the current module whose contents correspond to
/// `src/bar/baz.eqlog`.
/// As before, the first argument is the rust module name.
/// The second argument is the path of the eqlog file relative to the `src` directory, but with the
/// `.rs` extension instead of .`eqlog`.
/// The path must start with a slash.
/// It is recommended that the rust module name agrees with the eqlog file name, and that the
/// declaration above is in `src/bar/mod.rs` or in `src/bar.rs`.
/// This results in the module path `bar::baz` relative the crate root.
///
/// Eqlog modules can be annotated with a visibility, or with attributes:
/// ```ignore
/// eqlog_mod!(#[cfg(test)] pub baz, "/bar/baz.rs")
/// ```
#[macro_export]
macro_rules! eqlog_mod {
    ($(#[$attr:meta])* $vis:vis $modname:ident) => {
        eqlog_mod!($(#[$attr])* $vis $modname, concat!("/", stringify!($modname), ".rs"));
    };

    ($(#[$attr:meta])* $vis:vis $modname:ident, $source:expr) => {
        $(#[$attr])* $vis mod $modname { include!(concat!(env!("OUT_DIR"), $source)); }
    };
}
