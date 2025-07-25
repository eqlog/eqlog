//! # The Rust core allocation and collections library
//!
//! This library provides smart pointers and collections for managing
//! heap-allocated values.
//!
//! This library, like core, normally doesn’t need to be used directly
//! since its contents are re-exported in the [`std` crate](../std/index.html).
//! Crates that use the `#![no_std]` attribute however will typically
//! not depend on `std`, so they’d use this crate instead.
//!
//! ## Boxed values
//!
//! The [`Box`] type is a smart pointer type. There can only be one owner of a
//! [`Box`], and the owner can decide to mutate the contents, which live on the
//! heap.
//!
//! This type can be sent among threads efficiently as the size of a `Box` value
//! is the same as that of a pointer. Tree-like data structures are often built
//! with boxes because each node often has only one owner, the parent.
//!
//! ## Reference counted pointers
//!
//! The [`Rc`] type is a non-threadsafe reference-counted pointer type intended
//! for sharing memory within a thread. An [`Rc`] pointer wraps a type, `T`, and
//! only allows access to `&T`, a shared reference.
//!
//! This type is useful when inherited mutability (such as using [`Box`]) is too
//! constraining for an application, and is often paired with the [`Cell`] or
//! [`RefCell`] types in order to allow mutation.
//!
//! ## Atomically reference counted pointers
//!
//! The [`Arc`] type is the threadsafe equivalent of the [`Rc`] type. It
//! provides all the same functionality of [`Rc`], except it requires that the
//! contained type `T` is shareable. Additionally, [`Arc<T>`][`Arc`] is itself
//! sendable while [`Rc<T>`][`Rc`] is not.
//!
//! This type allows for shared access to the contained data, and is often
//! paired with synchronization primitives such as mutexes to allow mutation of
//! shared resources.
//!
//! ## Collections
//!
//! Implementations of the most common general purpose data structures are
//! defined in this library. They are re-exported through the
//! [standard collections library](../std/collections/index.html).
//!
//! ## Heap interfaces
//!
//! The [`alloc`](alloc/index.html) module defines the low-level interface to the
//! default global allocator. It is not compatible with the libc allocator API.
//!
//! [`Arc`]: sync
//! [`Box`]: boxed
//! [`Cell`]: core::cell
//! [`Rc`]: rc
//! [`RefCell`]: core::cell

#![allow(incomplete_features)]
#![allow(unused_attributes)]
#![doc(
    html_playground_url = "https://play.rust-lang.org/",
    issue_tracker_base_url = "https://github.com/rust-lang/rust/issues/",
    test(no_crate_inject, attr(allow(unused_variables), deny(warnings)))
)]
// Lints:
#![deny(unsafe_op_in_unsafe_fn)]
#![allow(explicit_outlives_requirements)]
#![allow(internal_features)]
#![allow(rustdoc::redundant_explicit_links)]
#![deny(ffi_unwind_calls)]
//
// Library features:
// tidy-alphabetical-start
#![feature(alloc_layout_extra)]
#![feature(allocator_api)]
#![feature(array_chunks)]
#![feature(array_into_iter_constructors)]
#![feature(array_windows)]
#![feature(ascii_char)]
#![feature(assert_matches)]
#![feature(async_fn_traits)]
#![feature(async_iterator)]
#![feature(bstr)]
#![feature(bstr_internals)]
#![feature(char_max_len)]
#![feature(clone_to_uninit)]
#![feature(coerce_unsized)]
#![feature(const_eval_select)]
#![feature(const_heap)]
#![feature(core_intrinsics)]
#![feature(deprecated_suggestion)]
#![feature(deref_pure_trait)]
#![feature(dispatch_from_dyn)]
#![feature(ergonomic_clones)]
#![feature(error_generic_member_access)]
#![feature(exact_size_is_empty)]
#![feature(extend_one)]
#![feature(extend_one_unchecked)]
#![feature(fmt_internals)]
#![feature(fn_traits)]
#![feature(formatting_options)]
#![feature(hasher_prefixfree_extras)]
#![feature(inplace_iteration)]
#![feature(iter_advance_by)]
#![feature(iter_next_chunk)]
#![feature(layout_for_ptr)]
#![feature(legacy_receiver_trait)]
#![feature(local_waker)]
#![feature(maybe_uninit_slice)]
#![feature(maybe_uninit_uninit_array_transpose)]
#![feature(panic_internals)]
#![feature(pattern)]
#![feature(pin_coerce_unsized_trait)]
#![feature(pointer_like_trait)]
#![feature(ptr_internals)]
#![feature(ptr_metadata)]
#![feature(set_ptr_value)]
#![feature(sized_type_properties)]
#![feature(slice_from_ptr_range)]
#![feature(slice_index_methods)]
#![feature(slice_iter_mut_as_mut_slice)]
#![feature(slice_ptr_get)]
#![feature(slice_range)]
#![feature(std_internals)]
#![feature(str_internals)]
#![feature(temporary_niche_types)]
#![feature(trusted_fused)]
#![feature(trusted_len)]
#![feature(trusted_random_access)]
#![feature(try_trait_v2)]
#![feature(try_with_capacity)]
#![feature(tuple_trait)]
#![feature(unicode_internals)]
#![feature(unsize)]
#![feature(unwrap_infallible)]
// tidy-alphabetical-end
//
// Language features:
// tidy-alphabetical-start
#![feature(allocator_internals)]
#![feature(allow_internal_unstable)]
#![feature(cfg_sanitize)]
#![feature(const_precise_live_drops)]
#![feature(coroutine_trait)]
#![feature(decl_macro)]
#![feature(dropck_eyepatch)]
#![feature(fundamental)]
#![feature(hashmap_internals)]
#![feature(intrinsics)]
#![feature(lang_items)]
#![feature(min_specialization)]
#![feature(multiple_supertrait_upcastable)]
#![feature(negative_impls)]
#![feature(never_type)]
#![feature(optimize_attribute)]
#![feature(rustc_allow_const_fn_unstable)]
#![feature(rustc_attrs)]
#![feature(slice_internals)]
#![feature(stmt_expr_attributes)]
#![feature(strict_provenance_lints)]
#![feature(unboxed_closures)]
#![feature(unsized_fn_params)]
#![feature(with_negative_coherence)]
#![rustc_preserve_ub_checks]
// tidy-alphabetical-end
//
// Rustdoc features:
#![feature(doc_cfg)]
#![feature(doc_cfg_hide)]
// Technically, this is a bug in rustdoc: rustdoc sees the documentation on `#[lang = slice_alloc]`
// blocks is for `&[T]`, which also has documentation using this feature in `core`, and gets mad
// that the feature-gate isn't enabled. Ideally, it wouldn't check for the feature gate for docs
// from other crates, but since this can only appear for lang items, it doesn't seem worth fixing.
#![feature(intra_doc_pointers)]

pub mod collections;
// These are there so that code in `collections` can use them via the crate root:
use std::alloc;
use std::boxed;
use std::vec;

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
