#[doc(hidden)]
pub mod btree_set;
mod types;
#[doc(hidden)]
pub mod unification;

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
#[used]
static TAG: &'static str = "EQLOG_RUNTIME_LIBRARY_TAG";

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
