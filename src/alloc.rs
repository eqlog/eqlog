//! Memory allocation APIs

#[doc(inline)]
pub use core::alloc::{AllocError, Allocator, Layout};
use core::hint;
use core::ptr::{self, NonNull};

/// The global memory allocator.
///
/// This type implements the [`Allocator`] trait by forwarding calls
/// to the allocator registered with the `#[global_allocator]` attribute
/// if there is one, or the `std` crate’s default.
///
/// Note: while this type is unstable, the functionality it provides can be
/// accessed through the [free functions in `alloc`](self#functions).
#[derive(Copy, Clone, Default, Debug)]
// the compiler needs to know when a Box uses the global allocator vs a custom one
pub struct Global;

/// Allocates memory with the global allocator.
///
/// This function forwards calls to the [`GlobalAlloc::alloc`] method
/// of the allocator registered with the `#[global_allocator]` attribute
/// if there is one, or the `std` crate’s default.
///
/// This function is expected to be deprecated in favor of the `allocate` method
/// of the [`Global`] type when it and the [`Allocator`] trait become stable.
///
/// # Safety
///
/// See [`GlobalAlloc::alloc`].
///
/// # Examples
///
/// ```
/// use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
///
/// unsafe {
///     let layout = Layout::new::<u16>();
///     let ptr = alloc(layout);
///     if ptr.is_null() {
///         handle_alloc_error(layout);
///     }
///
///     *(ptr as *mut u16) = 42;
///     assert_eq!(*(ptr as *mut u16), 42);
///
///     dealloc(ptr, layout);
/// }
/// ```
#[must_use = "losing the pointer will leak memory"]
#[inline]
#[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
pub unsafe fn alloc(layout: Layout) -> *mut u8 {
    std::alloc::alloc(layout)
}

/// Deallocates memory with the global allocator.
///
/// This function forwards calls to the [`GlobalAlloc::dealloc`] method
/// of the allocator registered with the `#[global_allocator]` attribute
/// if there is one, or the `std` crate’s default.
///
/// This function is expected to be deprecated in favor of the `deallocate` method
/// of the [`Global`] type when it and the [`Allocator`] trait become stable.
///
/// # Safety
///
/// See [`GlobalAlloc::dealloc`].
#[inline]
#[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
pub unsafe fn dealloc(ptr: *mut u8, layout: Layout) {
    unsafe { __rust_dealloc(ptr, layout.size(), layout.align()) }
}

/// Reallocates memory with the global allocator.
///
/// This function forwards calls to the [`GlobalAlloc::realloc`] method
/// of the allocator registered with the `#[global_allocator]` attribute
/// if there is one, or the `std` crate’s default.
///
/// This function is expected to be deprecated in favor of the `grow` and `shrink` methods
/// of the [`Global`] type when it and the [`Allocator`] trait become stable.
///
/// # Safety
///
/// See [`GlobalAlloc::realloc`].
#[must_use = "losing the pointer will leak memory"]
#[inline]
#[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
pub unsafe fn realloc(ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
    unsafe { __rust_realloc(ptr, layout.size(), layout.align(), new_size) }
}

/// Allocates zero-initialized memory with the global allocator.
///
/// This function forwards calls to the [`GlobalAlloc::alloc_zeroed`] method
/// of the allocator registered with the `#[global_allocator]` attribute
/// if there is one, or the `std` crate’s default.
///
/// This function is expected to be deprecated in favor of the `allocate_zeroed` method
/// of the [`Global`] type when it and the [`Allocator`] trait become stable.
///
/// # Safety
///
/// See [`GlobalAlloc::alloc_zeroed`].
///
/// # Examples
///
/// ```
/// use std::alloc::{alloc_zeroed, dealloc, handle_alloc_error, Layout};
///
/// unsafe {
///     let layout = Layout::new::<u16>();
///     let ptr = alloc_zeroed(layout);
///     if ptr.is_null() {
///         handle_alloc_error(layout);
///     }
///
///     assert_eq!(*(ptr as *mut u16), 0);
///
///     dealloc(ptr, layout);
/// }
/// ```
#[must_use = "losing the pointer will leak memory"]
#[inline]
#[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
pub unsafe fn alloc_zeroed(layout: Layout) -> *mut u8 {
    std::alloc::alloc_zeroed(layout)
}

impl Global {
    #[inline]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    fn alloc_impl(&self, layout: Layout, zeroed: bool) -> Result<NonNull<[u8]>, AllocError> {
        match layout.size() {
            0 => Ok(NonNull::slice_from_raw_parts(layout.dangling(), 0)),
            // SAFETY: `layout` is non-zero in size,
            size => unsafe {
                let raw_ptr = if zeroed { alloc_zeroed(layout) } else { alloc(layout) };
                let ptr = NonNull::new(raw_ptr).ok_or(AllocError)?;
                Ok(NonNull::slice_from_raw_parts(ptr, size))
            },
        }
    }

    // SAFETY: Same as `Allocator::grow`
    #[inline]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    unsafe fn grow_impl(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
        zeroed: bool,
    ) -> Result<NonNull<[u8]>, AllocError> {
        debug_assert!(
            new_layout.size() >= old_layout.size(),
            "`new_layout.size()` must be greater than or equal to `old_layout.size()`"
        );

        match old_layout.size() {
            0 => self.alloc_impl(new_layout, zeroed),

            // SAFETY: `new_size` is non-zero as `old_size` is greater than or equal to `new_size`
            // as required by safety conditions. Other conditions must be upheld by the caller
            old_size if old_layout.align() == new_layout.align() => unsafe {
                let new_size = new_layout.size();

                // `realloc` probably checks for `new_size >= old_layout.size()` or something similar.
                hint::assert_unchecked(new_size >= old_layout.size());

                let raw_ptr = realloc(ptr.as_ptr(), old_layout, new_size);
                let ptr = NonNull::new(raw_ptr).ok_or(AllocError)?;
                if zeroed {
                    raw_ptr.add(old_size).write_bytes(0, new_size - old_size);
                }
                Ok(NonNull::slice_from_raw_parts(ptr, new_size))
            },

            // SAFETY: because `new_layout.size()` must be greater than or equal to `old_size`,
            // both the old and new memory allocation are valid for reads and writes for `old_size`
            // bytes. Also, because the old allocation wasn't yet deallocated, it cannot overlap
            // `new_ptr`. Thus, the call to `copy_nonoverlapping` is safe. The safety contract
            // for `dealloc` must be upheld by the caller.
            old_size => unsafe {
                let new_ptr = self.alloc_impl(new_layout, zeroed)?;
                ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_mut_ptr(), old_size);
                self.deallocate(ptr, old_layout);
                Ok(new_ptr)
            },
        }
    }
}

unsafe impl Allocator for Global {
    #[inline]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        self.alloc_impl(layout, false)
    }

    #[inline]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    fn allocate_zeroed(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        self.alloc_impl(layout, true)
    }

    #[inline]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        if layout.size() != 0 {
            // SAFETY:
            // * We have checked that `layout` is non-zero in size.
            // * The caller is obligated to provide a layout that "fits", and in this case,
            //   "fit" always means a layout that is equal to the original, because our
            //   `allocate()`, `grow()`, and `shrink()` implementations never returns a larger
            //   allocation than requested.
            // * Other conditions must be upheld by the caller, as per `Allocator::deallocate()`'s
            //   safety documentation.
            unsafe { dealloc(ptr.as_ptr(), layout) }
        }
    }

    #[inline]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        // SAFETY: all conditions must be upheld by the caller
        unsafe { self.grow_impl(ptr, old_layout, new_layout, false) }
    }

    #[inline]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    unsafe fn grow_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        // SAFETY: all conditions must be upheld by the caller
        unsafe { self.grow_impl(ptr, old_layout, new_layout, true) }
    }

    #[inline]
    #[cfg_attr(miri, track_caller)] // even without panics, this helps for Miri backtraces
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        debug_assert!(
            new_layout.size() <= old_layout.size(),
            "`new_layout.size()` must be smaller than or equal to `old_layout.size()`"
        );

        match new_layout.size() {
            // SAFETY: conditions must be upheld by the caller
            0 => unsafe {
                self.deallocate(ptr, old_layout);
                Ok(NonNull::slice_from_raw_parts(new_layout.dangling(), 0))
            },

            // SAFETY: `new_size` is non-zero. Other conditions must be upheld by the caller
            new_size if old_layout.align() == new_layout.align() => unsafe {
                // `realloc` probably checks for `new_size <= old_layout.size()` or something similar.
                hint::assert_unchecked(new_size <= old_layout.size());

                let raw_ptr = realloc(ptr.as_ptr(), old_layout, new_size);
                let ptr = NonNull::new(raw_ptr).ok_or(AllocError)?;
                Ok(NonNull::slice_from_raw_parts(ptr, new_size))
            },

            // SAFETY: because `new_size` must be smaller than or equal to `old_layout.size()`,
            // both the old and new memory allocation are valid for reads and writes for `new_size`
            // bytes. Also, because the old allocation wasn't yet deallocated, it cannot overlap
            // `new_ptr`. Thus, the call to `copy_nonoverlapping` is safe. The safety contract
            // for `dealloc` must be upheld by the caller.
            new_size => unsafe {
                let new_ptr = self.allocate(new_layout)?;
                ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_mut_ptr(), new_size);
                self.deallocate(ptr, old_layout);
                Ok(new_ptr)
            },
        }
    }
}
