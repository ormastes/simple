//! Command-line arguments, seeded by the SimpleOS `_start` stub.

use crate::ffi::{CStr, OsString};
use crate::fmt;
use crate::os::simpleos::ffi::OsStringExt;
use crate::sync::OnceLock;
use crate::vec;

/// Captured, immutable process arguments. Populated by [`init`] before `main`.
static ARGS: OnceLock<Vec<OsString>> = OnceLock::new();

/// Seed the argument store. Called from `pal::init` which runs exactly once.
///
/// # Safety
/// `argv` must point to `argc` null-terminated C strings and remain valid for
/// the lifetime of the process.
pub unsafe fn init(argc: isize, argv: *const *const u8) {
    if argc <= 0 || argv.is_null() {
        let _ = ARGS.set(Vec::new());
        return;
    }
    let mut v = Vec::with_capacity(argc as usize);
    for i in 0..argc {
        let p = unsafe { *argv.offset(i) };
        if p.is_null() {
            break;
        }
        let bytes = unsafe { CStr::from_ptr(p as *const i8).to_bytes() };
        v.push(OsString::from_vec(bytes.to_vec()));
    }
    let _ = ARGS.set(v);
}

pub struct Args {
    iter: vec::IntoIter<OsString>,
}

impl fmt::Debug for Args {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter.as_slice()).finish()
    }
}

pub fn args() -> Args {
    let v = ARGS.get().cloned().unwrap_or_default();
    Args {
        iter: v.into_iter(),
    }
}

impl Iterator for Args {
    type Item = OsString;
    fn next(&mut self) -> Option<OsString> {
        self.iter.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl ExactSizeIterator for Args {
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl DoubleEndedIterator for Args {
    fn next_back(&mut self) -> Option<OsString> {
        self.iter.next_back()
    }
}
