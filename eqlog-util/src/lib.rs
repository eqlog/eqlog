mod unification;

pub use crate::unification::Unification;
pub extern crate tabled;

#[macro_export]
macro_rules! eqlog_mod {
    ($(#[$attr:meta])* $vis:vis $modname:ident) => {
        eqlog_mod!($(#[$attr])* $vis $modname, concat!("/", stringify!($modname), ".rs"));
    };

    ($(#[$attr:meta])* $vis:vis $modname:ident, $source:expr) => {
        $(#[$attr])* $vis mod $modname { include!(concat!(env!("OUT_DIR"), $source)); }
    };
}
