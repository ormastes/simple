//! SimpleOS is single-threaded today — all thread ops return Unsupported.

use crate::ffi::CStr;
use crate::io;
use crate::num::NonZero;
use crate::time::Duration;

pub struct Thread(!);

pub const DEFAULT_MIN_STACK_SIZE: usize = 64 * 1024;

impl Thread {
    pub unsafe fn new(_stack: usize, _p: Box<dyn FnOnce()>) -> io::Result<Thread> {
        Err(io::Error::from(io::ErrorKind::Unsupported))
    }
    pub fn yield_now() {}
    pub fn set_name(_name: &CStr) {}
    pub fn sleep(_dur: Duration) {}
    pub fn join(self) {
        self.0
    }
}

pub fn available_parallelism() -> io::Result<NonZero<usize>> {
    NonZero::new(1).ok_or_else(|| io::Error::from(io::ErrorKind::Unsupported))
}

pub mod guard {
    pub type Guard = !;
    pub unsafe fn current() -> Option<Guard> {
        None
    }
    pub unsafe fn init() -> Option<Guard> {
        None
    }
}
