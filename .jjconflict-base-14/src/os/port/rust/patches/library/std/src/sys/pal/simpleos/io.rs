//! Copied verbatim from `sys/pal/unsupported/io.rs` so downstream libstd code
//! can depend on `IoSlice` / `IoSliceMut` without conditional compilation.

use crate::marker::PhantomData;
use crate::slice;

#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct IoSlice<'a> {
    vec: &'a [u8],
    _p: PhantomData<&'a u8>,
}

impl<'a> IoSlice<'a> {
    #[inline]
    pub fn new(buf: &'a [u8]) -> IoSlice<'a> {
        IoSlice {
            vec: buf,
            _p: PhantomData,
        }
    }
    #[inline]
    pub fn advance(&mut self, n: usize) {
        self.vec = &self.vec[n..];
    }
    #[inline]
    pub fn as_slice(&self) -> &'a [u8] {
        self.vec
    }
}

#[repr(transparent)]
pub struct IoSliceMut<'a> {
    vec: &'a mut [u8],
    _p: PhantomData<&'a mut u8>,
}

impl<'a> IoSliceMut<'a> {
    #[inline]
    pub fn new(buf: &'a mut [u8]) -> IoSliceMut<'a> {
        IoSliceMut {
            vec: buf,
            _p: PhantomData,
        }
    }
    #[inline]
    pub fn advance(&mut self, n: usize) {
        let tmp = core::mem::take(&mut self.vec);
        self.vec = &mut tmp[n..];
    }
    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        self.vec
    }
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        self.vec
    }
}

pub const fn is_terminal(_: &impl crate::os::fd::AsFd) -> bool {
    false
}

// Re-export primitives some libstd modules expect.
pub use core::slice::Iter as BufIter;
pub use slice::from_raw_parts as raw_parts;
