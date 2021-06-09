//! A library to ensure that a pointer is aligned and not null when it dereferences.

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
