//! A module containing functions defined in [`core::ptr`] with null and alignment checks.

use crate::is_aligned;
use crate::Error;
use crate::ERR_MSG;

/// The wrapper of `*p` which panics if `p` is either null or not aligned.
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
/// assert_eq!(unsafe { ptr::get(p) }, 3);
/// ```
pub unsafe fn get<T: Copy>(p: *const T) -> T {
    // SAFETY: The caller must uphold the all safety rules.
    unsafe { try_get(p).expect(ERR_MSG) }
}

/// The wrapper of `*p` which returns an error if the pointer is either null or not aligned.
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
/// let p: *const i32 = core::ptr::null();
/// assert_eq!(unsafe { ptr::try_get(p) }, Err(Error::Null));
///
/// let p = 0x1001 as *const i32;
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

/// The wrapper of `&mut *p` which panics if `p` is either null or not aligned.
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
/// let mut x = 3;
/// let p = &mut x as *mut i32;
/// let r = unsafe { ptr::as_mut(p) };
/// *r = 4;
/// assert_eq!(x, 4);
/// ```
pub unsafe fn as_mut<'a, T>(p: *mut T) -> &'a mut T {
    // SAFETY: The caller must uphold the all safety notes.
    unsafe { try_as_mut(p).expect(ERR_MSG) }
}

/// The wrapper of `&mut *p` which may return an error if `p` is either null or not aligned.
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
/// let mut x = 3;
/// let p = &mut x as *mut i32;
/// let r = unsafe { ptr::try_as_mut(p) };
///
/// if let Ok(r) = r {
///     *r = 4;
///     assert_eq!(x, 4);
/// } else {
///     unreachable!();
/// }
///
/// let mut p: *mut i32 = core::ptr::null_mut();
/// let r = unsafe { ptr::try_as_mut(p) };
/// assert_eq!(r, Err(Error::Null));
///
/// let mut p = 0x1001 as *mut i32;
/// let r = unsafe { ptr::try_as_mut(p) };
/// assert_eq!(r, Err(Error::NotAligned));
/// ```
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

/// The wrapper of `&*p` which panics if `p` is either null or not aligned.
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
/// let x = 3;
/// let p = &x as *const i32;
/// let r = unsafe { ptr::as_ref(p) };
/// assert_eq!(*r, 3);
/// ```
pub unsafe fn as_ref<'a, T>(p: *const T) -> &'a T {
    // SAFETY: The caller must uphold the all safety rules.
    unsafe { try_as_ref(p).expect(ERR_MSG) }
}

/// The wrapper of `&*p` which may return an error if `p` is either null or not aligned.
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
/// let x = 3;
/// let p = &x as *const i32;
/// let r = unsafe { ptr::try_as_ref(p) };
///
/// assert_eq!(r, Ok(&3));
///
/// let p: *const i32 = core::ptr::null();
/// let r = unsafe { ptr::try_as_ref(p) };
/// assert_eq!(r, Err(Error::Null));
///
/// let mut p = 0x1001 as *const i32;
/// let r = unsafe { ptr::try_as_ref(p) };
/// assert_eq!(r, Err(Error::NotAligned));
/// ```
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

/// The wrapper of [`core::ptr::read`] which panics if the passed pointer is either null or not
/// aligned.
///
/// # Safety
///
/// The caller must follow the safety rules required by [`core::ptr::read`] except the alignment and null
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
/// let x = 3;
/// let p = &x as *const _;
///
/// assert_eq!(unsafe { ptr::read(p) }, 3);
/// ```
pub unsafe fn read<T>(p: *const T) -> T {
    // SAFETY: The caller must uphold the all safety rules.
    unsafe { try_read(p).expect(ERR_MSG) }
}

/// The wrapper of [`core::ptr::read`] which may return an error if the passed pointer is either
/// null or not null.
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
///
/// # Examples
///
/// ```rust
/// use aligned::ptr;
/// use aligned::Error;
///
/// let x = 3;
/// let p = &x as *const _;
///
/// assert_eq!(unsafe { ptr::try_read(p) }, Ok(3));
///
/// let p: *const i32 = core::ptr::null();
/// assert_eq!(unsafe { ptr::try_read(p) }, Err(Error::Null));
///
/// let p = 0x1001 as *const i32;
/// assert_eq!(unsafe { ptr::try_read(p) }, Err(Error::NotAligned));
/// ```
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

/// The wrapper of [`core::ptr::write`] which panics if the passed pointer is either null or not
/// aligned.
///
/// # Safety
///
/// The caller must follow the safety rules required by [`core::ptr::write`] except the alignment
/// and null rules.
///
/// # Panics
///
/// This method panics if `p` is either null or not aligned correctly.
///
/// # Examples
///
/// ```rust
/// use aligned::ptr;
/// use aligned::Error;
///
/// let mut x = 3;
/// let p = &mut x as *mut i32;
///
/// unsafe { ptr::write(p, 4) };
///
/// assert_eq!(x, 4);
/// ```
pub unsafe fn write<T>(p: *mut T, v: T) {
    // SAFETY: The caller must uphold the all safety rules.
    unsafe { try_write(p, v).expect(ERR_MSG) }
}

/// The wrapper of [`core::ptr::write`] which may return an error if the passed pointer is either
/// null or not aligned.
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
///
/// # Examples
///
/// ```rust
/// use aligned::ptr;
/// use aligned::Error;
///
/// let mut x = 3;
/// let p = &mut x as *mut i32;
///
/// let r = unsafe { ptr::try_write(p, 4) };
/// assert!(r.is_ok());
/// assert_eq!(x, 4);
///
/// let p: *mut i32 = core::ptr::null_mut();
/// let r = unsafe { ptr::try_write(p, 4) };
/// assert_eq!(r, Err(Error::Null));
///
/// let p = 0x1001 as *mut i32;
/// let r = unsafe { ptr::try_write(p, 4) };
/// assert_eq!(r, Err(Error::NotAligned));
/// ```
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
