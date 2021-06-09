//! A module containing functions defined in [`core::ptr`] with null and alignment checks.

use crate::return_error_on_null_or_misaligned;
use crate::Result;
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
/// This function panics if `p` is either null or not aligned correctly.
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
/// This function may return an error:
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
pub unsafe fn try_get<T: Copy>(p: *const T) -> Result<T> {
    return_error_on_null_or_misaligned(p)?;

    // SAFETY: The caller must uphold the all safety rules.
    Ok(unsafe { *p })
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
/// This function panics if `p` is either null or not aligned correctly.
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
/// This function may return an error:
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
pub unsafe fn try_as_mut<'a, T>(p: *mut T) -> Result<&'a mut T> {
    return_error_on_null_or_misaligned(p)?;

    // SAFETY: The caller must uphold the all safety rules.
    Ok(unsafe { &mut *p })
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
/// This function panics if `p` is either null or not aligned correctly.
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
/// This function may return an error:
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
pub unsafe fn try_as_ref<'a, T>(p: *const T) -> Result<&'a T> {
    return_error_on_null_or_misaligned(p)?;

    // SAFETY: The caller must uphold the all safety rules.
    Ok(unsafe { &*p })
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
/// This function panics if `p` is either null or not aligned correctly.
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
/// This function may return an error:
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
pub unsafe fn try_read<T>(p: *const T) -> Result<T> {
    return_error_on_null_or_misaligned(p)?;

    Ok(unsafe { p.read() })
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
/// This function panics if `p` is either null or not aligned correctly.
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
/// This function may return an error:
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
pub unsafe fn try_write<T>(p: *mut T, v: T) -> Result<()> {
    return_error_on_null_or_misaligned(p)?;

    // SAFETY: The caller must uphold the all safety rules.
    unsafe { p.write(v) };
    Ok(())
}

/// The wrapper of [`core::ptr::copy`] which panics unless the passed pointers are aligned and not
/// null.
///
/// # Safety
///
/// The caller must follow the safety rules required by [`core::ptr::copy`] except the alignment
/// and null rules.
///
/// # Examples
///
/// ```rust
/// use aligned::ptr;
/// use core::mem::MaybeUninit;
///
/// let x = 3;
/// let src = &x as *const i32;
/// let mut y = MaybeUninit::uninit();
/// let dst = y.as_mut_ptr();
///
/// unsafe { ptr::copy(src, dst, 1) };
/// let y = unsafe { y.assume_init() };
/// assert_eq!(y, 3);
/// ```
pub unsafe fn copy<T>(src: *const T, dst: *mut T, count: usize) {
    // SAFETY: The caller must uphold the all safety rules.
    unsafe { try_copy(src, dst, count).expect(ERR_MSG) }
}

/// The wrapper of [`core::ptr::copy`] which may return an error unless the passed pointers are
/// aligned and not null.
///
/// # Safety
///
/// The caller must follow the safety rules required by [`core::ptr::copy`] except the alignment
/// and null rules.
///
/// # Errors
///
/// This function may return an error:
///
/// - [`Error::Null`] - Either `src` or `dst` is null.
/// - [`Error::NotAligned`] - Either `src` or `dst` is not aligned correctly.
///
/// # Examples
///
/// ```rust
/// use aligned::ptr;
/// use aligned::Error;
/// use core::mem::MaybeUninit;
///
/// let x = 3;
/// let src = &x as *const i32;
/// let mut y = MaybeUninit::uninit();
/// let dst = y.as_mut_ptr();
///
/// let r = unsafe { ptr::try_copy(src, dst, 1) };
/// assert!(r.is_ok());
/// let y = unsafe { y.assume_init() };
/// assert_eq!(y, 3);
///
/// let dst = core::ptr::null_mut();
/// let r = unsafe { ptr::try_copy(src, dst, 1) };
/// assert_eq!(r, Err(Error::Null));
///
/// let dst = 0x1001 as *mut i32;
/// let r = unsafe { ptr::try_copy(src, dst, 1) };
/// assert_eq!(r, Err(Error::NotAligned));
/// ```
pub unsafe fn try_copy<T>(src: *const T, dst: *mut T, count: usize) -> Result<()> {
    return_error_on_null_or_misaligned(src)?;
    return_error_on_null_or_misaligned(dst)?;

    // SAFETY: The caller must uphold the all safety rules.
    unsafe { core::ptr::copy(src, dst, count) };
    Ok(())
}

/// The wrapper of [`core::ptr::copy_nonoverlapping`] which panics unless the passed pointers are aligned and not
/// null.
///
/// # Safety
///
/// The caller must follow the safety rules required by [`core::ptr::copy_nonoverlapping`] except the alignment
/// and null rules.
///
/// # Examples
///
/// ```rust
/// use aligned::ptr;
/// use core::mem::MaybeUninit;
///
/// let x = 3;
/// let src = &x as *const i32;
/// let mut y = MaybeUninit::uninit();
/// let dst = y.as_mut_ptr();
///
/// unsafe { ptr::copy_nonoverlapping(src, dst, 1) };
/// let y = unsafe { y.assume_init() };
/// assert_eq!(y, 3);
/// ```
pub unsafe fn copy_nonoverlapping<T>(src: *const T, dst: *mut T, count: usize) {
    // SAFETY: The caller must uphold the all safety rules.
    unsafe { try_copy_nonoverlapping(src, dst, count).expect(ERR_MSG) }
}

/// The wrapper of [`core::ptr::copy_nonoverlapping`] which returns an error unless the passed
/// pointers are aligned and not null.
///
/// # Safety
///
/// The caller must follow the safety rules required by [`core::ptr::copy_nonoverlapping`] except
/// the alignment and null rules.
///
/// # Errors
///
/// This function may return an error:
///
/// - [`Error::Null`] - Either `src` or `dst` is null.
/// - [`Error::NotAligned`] - Either `src` or `dst` is not aligned.
///
/// # Examples
///
/// ```rust
/// use aligned::ptr;
/// use aligned::Error;
/// use core::mem::MaybeUninit;
///
/// let x = 3;
/// let src = &x as *const i32;
/// let mut y = MaybeUninit::uninit();
/// let dst = y.as_mut_ptr();
///
/// let r = unsafe { ptr::try_copy_nonoverlapping(src, dst, 1) };
/// assert!(r.is_ok());
/// let y = unsafe { y.assume_init() };
/// assert_eq!(y, 3);
///
/// let dst = core::ptr::null_mut();
/// let r = unsafe { ptr::try_copy_nonoverlapping(src, dst, 1) };
/// assert_eq!(r, Err(Error::Null));
///
/// let dst = 0x1001 as *mut i32;
/// let r = unsafe { ptr::try_copy_nonoverlapping(src, dst, 1) };
/// assert_eq!(r, Err(Error::NotAligned));
/// ```
pub unsafe fn try_copy_nonoverlapping<T>(src: *const T, dst: *mut T, count: usize) -> Result<()> {
    return_error_on_null_or_misaligned(src)?;
    return_error_on_null_or_misaligned(dst)?;

    // SAFETY: The caller must uphold the all safety rules.
    unsafe { core::ptr::copy_nonoverlapping(src, dst, count) };

    Ok(())
}

/// The wraper of [`core::ptr::drop_in_place`] which returns an error if the passed pointer is null
/// or not aligned.
///
/// Note that the original function accepts types which are not [`Sized`]. However, this function
/// only accepts types which are [`Sized`].
///
/// # Safety
///
/// The caller must follow the safety rules required by [`core::ptr::drop_in_place`] except the
/// alignment and null rules.
///
/// # Errors
///
/// This function may return an error:
///
/// - [`Error::Null`] - `to_drop` is null.
/// - [`Error::NotAligned`] - `to_drop` is not aligned.
///
/// # Examples
///
/// ```rust
/// use aligned::ptr;
/// use aligned::Error;
///
/// let b = Box::new(3);
/// let p = Box::into_raw(b);
/// let r = unsafe { ptr::try_drop_in_place(p) };
/// assert!(r.is_ok());
///
/// let p: *mut i32 = core::ptr::null_mut();
/// let r = unsafe { ptr::try_drop_in_place(p) };
/// assert_eq!(r, Err(Error::Null));
///
/// let p = 0x1001 as *mut i32;
/// let r = unsafe { ptr::try_drop_in_place(p) };
/// assert_eq!(r, Err(Error::NotAligned));
/// ```
pub unsafe fn try_drop_in_place<T>(to_drop: *mut T) -> Result<()> {
    return_error_on_null_or_misaligned(to_drop)?;

    // SAFETY: The caller must uphold the all safety rules.
    unsafe { core::ptr::drop_in_place(to_drop) };
    Ok(())
}
