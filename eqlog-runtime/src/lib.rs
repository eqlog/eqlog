// This is here to support our cursed way of finding the eqlog runtime rlib file in the cargo
// target directory. Cargo does not let build scripts know where it put rlib files of dependencies.
// The build script in a crate that compiles eqlog modules must know where the rlib is though (at
// least for component builds) so that it can pass the eqlog runtime rlib path as --extern
// parameter to rustc when compiling eqlog modules.
//
// As a workaround, the build script scans the target directory for files that look like they might
// be the eqlog runtime rlib file. I haven't found a way to narrow this down to a single file
// though; there are several libeqlog_runtime-<hash>.rlib files. I think they might be there for
// macros and for the build script of the runtime crate. We're only interested in the actual
// runtime crate from this crate though. To find this file, the build script scans the .rlib file
// for the value of the TAG variable below.
//
// We also can't use a fixed tag value here because I think eqlog-runtime is built twice depending
// on whether it's a dependency for the build script or the crate itself. To single it down, we use
// the OUT_DIR variable as part of the tag. The OUT_DIR variable is also available in the buidl
// script of eqlog-runtime, which emits its value as link metadata value, see the cargo "link"
// feature. This metadata value is then available in the build scripts of crates that dependend on
// eqlog-runtime. The eqlog compiler crate can thus read it and scan potential eqlog-runtime rlib
// for whether they contain this tag.
#[used]
static TAG: &'static str = concat!("EQLOG_RUNTIME_TAG_", env!("OUT_DIR"));

mod prefix_tree;
mod unification;
#[doc(hidden)]
pub mod wbtree_map;

#[doc(hidden)]
pub use crate::prefix_tree::{
    PrefixTree0, PrefixTree1, PrefixTree2, PrefixTree3, PrefixTree4, PrefixTree5, PrefixTree6,
    PrefixTree7, PrefixTree8, PrefixTree9,
};
#[doc(hidden)]
pub use crate::unification::Unification;

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
