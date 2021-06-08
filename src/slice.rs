//! A module containing functions defined in [`core::slice`] with null and alignment checks.

use crate::is_aligned;
use crate::Error;
use crate::ERR_MSG;

/// Creates a mutable reference to a slice with [`core::slice::from_raw_parts_mut`].
///
/// # Safety
///
/// The caller must follow the rules required by [`core::slice::from_raw_parts_mut`] except the
/// alignment and null rules.
pub unsafe fn from_raw_parts_mut<'a, T>(data: *mut T, len: usize) -> &'a mut [T] {
    // SAFETY: The caller must uphold the all safety rules.
    let r = unsafe { try_from_raw_parts_mut(data, len) };
    r.expect(ERR_MSG)
}

/// Creates a mutable reference to a slice with [`core::slice::from_raw_parts_mut`]
///
/// # Safety
///
/// The caller must follow the rules required by [`core::slice::from_raw_parts_mut`] except the
/// alignment and null rules.
///
/// # Errors
///
/// This method may return an error:
///
/// - [`Error::Null`] - `p` is null.
/// - [`Error::NotAligned`] - `p` is not aligned correctly.
pub unsafe fn try_from_raw_parts_mut<'a, T>(
    data: *mut T,
    len: usize,
) -> Result<&'a mut [T], Error> {
    if data.is_null() {
        Err(Error::Null)
    } else if is_aligned(data) {
        // SAFETY: The caller must uphold the all safety rules.
        Ok(unsafe { core::slice::from_raw_parts_mut(data, len) })
    } else {
        Err(Error::NotAligned)
    }
}
