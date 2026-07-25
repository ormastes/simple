//! SimpleOS-specific extensions to primitives in the [`std::ffi`] module.
//!
//! SimpleOS stores `OsString` as a `Vec<u8>` internally (see
//! `sys::os_str::Buf`), so the extension traits here are a byte-for-byte
//! port of the `std::os::unix::ffi` / `std::os::hermit::ffi` surface.
//!
//! [`std::ffi`]: crate::ffi

#![stable(feature = "rust1", since = "1.0.0")]

use crate::ffi::{OsStr, OsString};
use crate::sealed::Sealed;
use crate::sys_common::{AsInner, FromInner, IntoInner};

/// SimpleOS-specific extensions to [`OsString`].
///
/// [`OsString`]: crate::ffi::OsString
#[stable(feature = "rust1", since = "1.0.0")]
pub trait OsStringExt: Sealed {
    /// Creates an [`OsString`] from a byte vector.
    #[stable(feature = "rust1", since = "1.0.0")]
    fn from_vec(vec: Vec<u8>) -> Self;

    /// Yields the underlying byte vector of this [`OsString`].
    #[stable(feature = "rust1", since = "1.0.0")]
    fn into_vec(self) -> Vec<u8>;
}

#[stable(feature = "rust1", since = "1.0.0")]
impl OsStringExt for OsString {
    #[inline]
    fn from_vec(vec: Vec<u8>) -> OsString {
        FromInner::from_inner(crate::sys::os_str::Buf { inner: vec })
    }
    #[inline]
    fn into_vec(self) -> Vec<u8> {
        self.into_inner().inner
    }
}

/// SimpleOS-specific extensions to [`OsStr`].
///
/// [`OsStr`]: crate::ffi::OsStr
#[stable(feature = "rust1", since = "1.0.0")]
pub trait OsStrExt: Sealed {
    /// Creates an [`OsStr`] from a byte slice.
    #[stable(feature = "rust1", since = "1.0.0")]
    fn from_bytes(slice: &[u8]) -> &Self;

    /// Gets the underlying byte view of the [`OsStr`] slice.
    #[stable(feature = "rust1", since = "1.0.0")]
    fn as_bytes(&self) -> &[u8];
}

#[stable(feature = "rust1", since = "1.0.0")]
impl OsStrExt for OsStr {
    #[inline]
    fn from_bytes(slice: &[u8]) -> &OsStr {
        unsafe { &*(slice as *const [u8] as *const OsStr) }
    }
    #[inline]
    fn as_bytes(&self) -> &[u8] {
        &self.as_inner().inner
    }
}
