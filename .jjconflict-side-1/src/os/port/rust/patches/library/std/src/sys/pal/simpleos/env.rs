//! Process environment shim. SimpleOS only implements `getenv` today.

use crate::ffi::{CStr, CString, OsStr, OsString};
use crate::io;
use crate::os::simpleos::ffi::{OsStrExt, OsStringExt};

unsafe extern "C" {
    fn getenv(name: *const i8) -> *const i8;
}

pub mod os {
    pub const FAMILY: &str = "unix";
    pub const OS: &str = "simpleos";
    pub const DLL_PREFIX: &str = "lib";
    pub const DLL_SUFFIX: &str = ".so";
    pub const DLL_EXTENSION: &str = "so";
    pub const EXE_SUFFIX: &str = "";
    pub const EXE_EXTENSION: &str = "";
}

pub fn var(key: &OsStr) -> Option<OsString> {
    // `getenv` wants a NUL-terminated string; non-representable keys bail.
    let cstr = CString::new(key.as_bytes()).ok()?;
    let ptr = unsafe { getenv(cstr.as_ptr()) };
    if ptr.is_null() {
        return None;
    }
    let bytes = unsafe { CStr::from_ptr(ptr) }.to_bytes().to_vec();
    Some(OsString::from_vec(bytes))
}

pub fn set_var(_k: &OsStr, _v: &OsStr) -> io::Result<()> {
    Err(io::Error::from(io::ErrorKind::Unsupported))
}

pub fn unset_var(_k: &OsStr) -> io::Result<()> {
    Err(io::Error::from(io::ErrorKind::Unsupported))
}

pub fn env() -> Env {
    Env { _priv: () }
}

pub struct Env {
    _priv: (),
}

impl Iterator for Env {
    type Item = (OsString, OsString);
    fn next(&mut self) -> Option<Self::Item> {
        None
    }
}
