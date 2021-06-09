//! A module containing functions defined in [`core::slice`] with null and alignment checks.

use crate::return_error_on_null_or_misaligned;
use crate::Result;
use crate::ERR_MSG;

/// The wrapper of [`core::slice::from_raw_parts_mut`] which panics if the passed pointer is either
/// null or not aligned.
///
/// # Safety
///
/// The caller must follow the rules required by [`core::slice::from_raw_parts_mut`] except the
/// alignment and null rules.
///
/// # Examples
///
/// ```rust
/// use aligned::slice;
///
/// let mut x = 3;
/// let s = unsafe { slice::from_raw_parts_mut(&mut x, 1) };
///
/// assert_eq!(s, [3]);
/// ```
pub unsafe fn from_raw_parts_mut<'a, T>(data: *mut T, len: usize) -> &'a mut [T] {
    // SAFETY: The caller must uphold the all safety rules.
    let r = unsafe { try_from_raw_parts_mut(data, len) };
    r.expect(ERR_MSG)
}

/// The wrapper of [`core::slice::from_raw_parts_mut`] which may return an error if the passed
/// pointer is either null or not aligned.
///
/// # Safety
///
/// The caller must follow the rules required by [`core::slice::from_raw_parts_mut`] except the
/// alignment and null rules.
///
/// # Errors
///
/// This function may return an error:
///
/// - [`crate::Error::Null`] - `p` is null.
/// - [`crate::Error::NotAligned`] - `p` is not aligned correctly.
///
/// # Examples
///
/// ```rust
/// use aligned::slice;
/// use aligned::Error;
///
/// let mut x = 3;
/// let s = unsafe { slice::try_from_raw_parts_mut(&mut x, 1) };
///
/// assert!(s.is_ok());
/// assert_eq!(s.unwrap(), [3]);
///
/// let p: *mut i32 = core::ptr::null_mut();
/// let s = unsafe { slice::try_from_raw_parts_mut(p, 1) };
/// assert_eq!(s, Err(Error::Null));
///
/// let p = 0x1001 as *mut i32;
/// let s = unsafe { slice::try_from_raw_parts_mut(p, 1) };
/// assert_eq!(s, Err(Error::NotAligned));
/// ```
pub unsafe fn try_from_raw_parts_mut<'a, T>(data: *mut T, len: usize) -> Result<&'a mut [T]> {
    return_error_on_null_or_misaligned(data)?;

    // SAFETY: The caller must uphold the all safety rules.
    Ok(unsafe { core::slice::from_raw_parts_mut(data, len) })
}
