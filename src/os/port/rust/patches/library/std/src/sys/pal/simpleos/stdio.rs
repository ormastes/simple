//! Unbuffered `Stdout` / `Stderr` backed by raw `write(2)` to fds 1 and 2.

use crate::io;

unsafe extern "C" {
    fn write(fd: i32, buf: *const u8, count: usize) -> isize;
}

pub struct Stdin;
pub struct Stdout;
pub struct Stderr;

pub const STDIN_BUF_SIZE: usize = 0;

impl Stdin {
    pub const fn new() -> Self {
        Stdin
    }
}

impl io::Read for Stdin {
    fn read(&mut self, _buf: &mut [u8]) -> io::Result<usize> {
        Ok(0)
    }
}

impl Stdout {
    pub const fn new() -> Self {
        Stdout
    }
}

impl io::Write for Stdout {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        write_fd(1, buf)
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl Stderr {
    pub const fn new() -> Self {
        Stderr
    }
}

impl io::Write for Stderr {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        write_fd(2, buf)
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

fn write_fd(fd: i32, buf: &[u8]) -> io::Result<usize> {
    // SAFETY: buffer pointer/length pair came from a Rust slice.
    let n = unsafe { write(fd, buf.as_ptr(), buf.len()) };
    if n < 0 {
        Err(io::Error::from(io::ErrorKind::Other))
    } else {
        Ok(n as usize)
    }
}

pub fn is_ebadf(_err: &io::Error) -> bool {
    false
}

pub fn panic_output() -> Option<impl io::Write> {
    Some(Stderr::new())
}
