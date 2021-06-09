//! A library to ensure that a pointer is aligned and not null when it dereferences.
//!
//! This crate contains wrappers of unsafe functions defined in [`core::ptr`] and [`core::slice`].
//! These wrappers panic or return errors if the passed pointers are null or not aligned correctly.
//!
//! For example, the code below panics because `p` is not aligned correctly.//!
//!
//! ```rust
//! use aligned::ptr;
//!
//! let x = 0xdead_beaf_u32;
//! let p = (&x as *const u32 as usize + 1) as *const u16;
//!
//! unsafe { ptr::read(p) };
//! ```
//!
//! If we import [`core::ptr`] instead of [`ptr`], the code may run successfully.
//! However, dereferencing unaligned pointer causes *undefined behavior* and must be avoided
//! by all means (except [`core::ptr::read_unaligned`] and [`core::ptr::write_unaligned`]).
//!
//! # Safety
//!
//! While the functions defined in this crate rejects unaligned or null pointers, the caller must
//! follow the other safety rules. For more information, see the safety note of [`core::ptr`].

#![no_std]
#![deny(rustdoc::all, unsafe_op_in_unsafe_fn)]

pub mod error;
pub mod ptr;
pub mod slice;

pub use error::Error;

/// [`core::result::Result`] which may contain [`Error`].
pub type Result<T> = core::result::Result<T, Error>;

const ERR_MSG: &str = "Pointer is either null or not aligned.";

fn return_error_on_null_or_misaligned<T>(p: *const T) -> Result<()> {
    if p.is_null() {
        Err(Error::Null)
    } else if is_aligned(p) {
        Ok(())
    } else {
        Err(Error::NotAligned)
    }
}

fn is_aligned<T>(p: *const T) -> bool {
    p as usize % core::mem::align_of::<T>() == 0
}
