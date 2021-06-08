//! A module containing functions defined in [`core::ptr`] with null and alignment checks.

use crate::is_aligned;
use crate::Error;
use crate::ERR_MSG;

/// Gets a value the pointer `p` points by dereferencing it.
///
/// # Safety
///
/// The caller must follow the safety rules listed at [`core::ptr`] except the alignment and null
/// rules.
///
/// # Panics
///
/// This method panics if `p` is either null or not aligned correctly.
///
/// # Examples
///
/// ```rust
/// use aligned::ptr;
///
/// let b = Box::new(3);
/// let p = Box::into_raw(b);
///
/// unsafe { assert_eq!(ptr::get(p), 3); }
/// ```
pub unsafe fn get<T: Copy>(p: *const T) -> T {
    // SAFETY: The caller must uphold the all safety rules.
    unsafe { try_get(p).expect(ERR_MSG) }
}

/// Gets a value the pointer `p` points by dereferencing it.
///
/// # Safety
///
/// The caller must follow the safety rules listed at [`core::ptr`] except the alignment and null
/// rules.
///
/// # Errors
///
/// This method may return an error:
///
/// - [`Error::Null`] - `p` is null.
/// - [`Error::NotAligned`] - `p` is not aligned correctly.
///
/// # Examples
///
/// ```rust
/// use aligned::ptr;
/// use aligned::Error;
///
/// let b = Box::new(3);
/// let p = Box::into_raw(b);
/// assert_eq!(unsafe { ptr::try_get(p) }, Ok(3));
///
/// let p: *const u32 = core::ptr::null();
/// assert_eq!(unsafe { ptr::try_get(p) }, Err(Error::Null));
///
/// let p = 0x1001 as *const u32;
/// assert_eq!(unsafe { ptr::try_get(p) }, Err(Error::NotAligned));
/// ```
pub unsafe fn try_get<T: Copy>(p: *const T) -> Result<T, Error> {
    if p.is_null() {
        Err(Error::Null)
    } else if is_aligned(p) {
        // SAFETY: The caller must uphold the all safety rules.
        Ok(unsafe { *p })
    } else {
        Err(Error::NotAligned)
    }
}

/// Converts a pointer to a mutable reference.
///
/// # Safety
///
/// The caller must follow the safety rules listed at [`core::ptr`] except the alignment and null
/// rules.
///
/// # Panics
///
/// This method panics if `p` is either null or not aligned correctly.
pub unsafe fn as_mut<'a, T>(p: *mut T) -> &'a mut T {
    // SAFETY: The caller must uphold the all safety notes.
    unsafe { try_as_mut(p).expect(ERR_MSG) }
}

/// Converts a pointer to a mutable reference.
///
/// # Safety
///
/// The caller must follow the safety rules listed at [`core::ptr`] except the alignment and null
/// rules.
///
/// # Errors
///
/// This method may return an error:
///
/// - [`Error::Null`] - `p` is null.
/// - [`Error::NotAligned`] - `p` is not aligned correctly.
pub unsafe fn try_as_mut<'a, T>(p: *mut T) -> Result<&'a mut T, Error> {
    if p.is_null() {
        Err(Error::Null)
    } else if is_aligned(p) {
        // SAFETY: The caller must uphold the all safety rules.
        Ok(unsafe { &mut *p })
    } else {
        Err(Error::NotAligned)
    }
}

/// Converts a pointer to an immutable reference.
///
/// # Safety
///
/// The caller must follow the safety rules listed at [`core::ptr`] except the alignment and null
/// rules.
///
/// # Panics
///
/// This method panics if `p` is either null or not aligned correctly.
pub unsafe fn as_ref<'a, T>(p: *const T) -> &'a T {
    // SAFETY: The caller must uphold the all safety rules.
    unsafe { try_as_ref(p).expect(ERR_MSG) }
}

/// Converts a pointer to an immutable reference.
///
/// # Safety
///
/// The caller must follow the safety rules listed at [`core::ptr`] except the alignment and null
/// rules.
///
/// # Errors
///
/// This method may return an error:
///
/// - [`Error::Null`] - `p` is null.
/// - [`Error::NotAligned`] - `p` is not aligned correctly.
pub unsafe fn try_as_ref<'a, T>(p: *const T) -> Result<&'a T, Error> {
    if p.is_null() {
        Err(Error::Null)
    } else if is_aligned(p) {
        // SAFETY: The caller must uphold the all safety rules.
        Ok(unsafe { &*p })
    } else {
        Err(Error::NotAligned)
    }
}

/// Reads a value the pointer `p` points with [`core::ptr::read`].
///
/// # Safety
///
/// The caller must follow the safety rules required by [`core::ptr::read`] except the alignment and null
/// rules.
///
/// # Panics
///
/// This method panics if `p` is either null or not aligned correctly.
pub unsafe fn read<T>(p: *const T) -> T {
    // SAFETY: The caller must uphold the all safety rules.
    unsafe { try_read(p).expect(ERR_MSG) }
}

/// Reads a value the pointer `p` points with [`core::ptr::read`].
///
/// # Safety
///
/// The caller must follow the safety rules required by [`core::ptr::read`] except the alignment
/// and null rules.
///
/// # Errors
///
/// This method may return an error:
///
/// - [`Error::Null`] - `p` is null.
/// - [`Error::NotAligned`] - `p` is not aligned correctly.
pub unsafe fn try_read<T>(p: *const T) -> Result<T, Error> {
    if p.is_null() {
        Err(Error::Null)
    } else if is_aligned(p) {
        // SAFETY: The caller must uphold the all safety rules.
        Ok(unsafe { p.read() })
    } else {
        Err(Error::NotAligned)
    }
}

/// Writes a value the pointer `p` points with [`core::ptr::write`].
///
/// # Safety
///
/// The caller must follow the safety rules required by [`core::ptr::write`] except the alignment
/// and null rules.
///
/// # Panics
///
/// This method panics if `p` is either null or not aligned correctly.
pub unsafe fn write<T>(p: *mut T, v: T) {
    // SAFETY: The caller must uphold the all safety rules.
    unsafe { try_write(p, v).expect(ERR_MSG) }
}

/// Writes a value the pointer `p` points with [`core::ptr::write`].
///
/// # Safety
///
/// The caller must follow the safety rules required by [`core::ptr::write`] except the alignment
/// and null rules.
///
/// # Errors
///
/// This method may return an error:
///
/// - [`Error::Null`] - `p` is null.
/// - [`Error::NotAligned`] - `p` is not aligned correctly.
pub unsafe fn try_write<T>(p: *mut T, v: T) -> Result<(), Error> {
    if p.is_null() {
        Err(Error::Null)
    } else if is_aligned(p) {
        // SAFETY: The caller must uphold the all safety rules.
        unsafe { p.write(v) };
        Ok(())
    } else {
        Err(Error::NotAligned)
    }
}
