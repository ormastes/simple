//! Minimal `fs` — `File::open`/`read`/`write` + `stat` on libsimpleos_c
//! syscalls. Directory iteration, rename, unlink, symlink are Unsupported.

use crate::ffi::{CString, OsString};
use crate::{fmt, io::{self, SeekFrom}, path::{Path, PathBuf}};
use crate::os::simpleos::ffi::OsStrExt;
use crate::sys_common::FromInner;

unsafe extern "C" {
    fn open(path: *const i8, flags: i32, mode: i32) -> i32;
    fn close(fd: i32) -> i32;
    fn read(fd: i32, buf: *mut u8, count: usize) -> isize;
    fn write(fd: i32, buf: *const u8, count: usize) -> isize;
    fn lseek(fd: i32, offset: i64, whence: i32) -> i64;
    fn stat(path: *const i8, buf: *mut RawStat) -> i32;
}

#[repr(C)]
#[derive(Default, Copy, Clone)]
pub struct RawStat { pub st_mode: u32, pub st_size: i64, pub st_mtime: i64 }

// <fcntl.h> constants from libsimpleos_c.
const O_RDONLY: i32 = 0; const O_WRONLY: i32 = 1; const O_RDWR: i32 = 2;
const O_CREAT: i32 = 0o100; const O_TRUNC: i32 = 0o1000; const O_APPEND: i32 = 0o2000;
const SEEK_SET: i32 = 0; const SEEK_CUR: i32 = 1; const SEEK_END: i32 = 2;

pub struct File(i32);
#[derive(Clone, Default)]
pub struct OpenOptions { read: bool, write: bool, append: bool, truncate: bool, create: bool, mode: i32 }
#[derive(Clone, Copy)] pub struct FilePermissions(u32);
#[derive(Clone)] pub struct FileAttr(RawStat);
#[derive(Clone, Copy)] pub struct FileType(u32);
pub struct ReadDir; pub struct DirEntry; pub struct DirBuilder;

impl fmt::Debug for File {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { f.debug_struct("File").field("fd", &self.0).finish() }
}

fn err_other<T>() -> io::Result<T> { Err(io::Error::from(io::ErrorKind::Other)) }
fn unsup<T>()     -> io::Result<T> { Err(io::Error::from(io::ErrorKind::Unsupported)) }

#[rustfmt::skip]
impl OpenOptions {
    pub fn new() -> Self { Self { mode: 0o666, ..Default::default() } }
    pub fn read(&mut self, v: bool)       { self.read = v; }
    pub fn write(&mut self, v: bool)      { self.write = v; }
    pub fn append(&mut self, v: bool)     { self.append = v; }
    pub fn truncate(&mut self, v: bool)   { self.truncate = v; }
    pub fn create(&mut self, v: bool)     { self.create = v; }
    pub fn create_new(&mut self, v: bool) { self.create = v; }
    pub fn mode(&mut self, m: u32)        { self.mode = m as i32; }

    fn as_flags(&self) -> i32 {
        let mut f = match (self.read, self.write | self.append) {
            (true,  true) => O_RDWR, (false, true) => O_WRONLY, _ => O_RDONLY,
        };
        if self.create   { f |= O_CREAT; }
        if self.truncate { f |= O_TRUNC; }
        if self.append   { f |= O_APPEND; }
        f
    }
}

#[rustfmt::skip]
impl File {
    pub fn open(p: &Path, o: &OpenOptions) -> io::Result<File> {
        let c = CString::new(p.as_os_str().as_bytes())
            .map_err(|_| io::Error::from(io::ErrorKind::InvalidInput))?;
        let fd = unsafe { open(c.as_ptr(), o.as_flags(), o.mode) };
        if fd < 0 { err_other() } else { Ok(File(fd)) }
    }
    pub fn read(&self, b: &mut [u8]) -> io::Result<usize> {
        let n = unsafe { read(self.0, b.as_mut_ptr(), b.len()) };
        if n < 0 { err_other() } else { Ok(n as usize) }
    }
    pub fn write(&self, b: &[u8]) -> io::Result<usize> {
        let n = unsafe { write(self.0, b.as_ptr(), b.len()) };
        if n < 0 { err_other() } else { Ok(n as usize) }
    }
    pub fn flush(&self) -> io::Result<()> { Ok(()) }
    pub fn seek(&self, pos: SeekFrom) -> io::Result<u64> {
        let (off, w) = match pos {
            SeekFrom::Start(n)   => (n as i64, SEEK_SET),
            SeekFrom::End(n)     => (n, SEEK_END),
            SeekFrom::Current(n) => (n, SEEK_CUR),
        };
        let r = unsafe { lseek(self.0, off, w) };
        if r < 0 { err_other() } else { Ok(r as u64) }
    }
    pub fn file_attr(&self) -> io::Result<FileAttr> { unsup() }
    pub fn duplicate(&self) -> io::Result<File>     { unsup() }
}

#[rustfmt::skip]
impl Drop for File {
    fn drop(&mut self) { unsafe { let _ = close(self.0); } }
}

pub fn stat_path(p: &Path) -> io::Result<FileAttr> {
    let c = CString::new(p.as_os_str().as_bytes())
        .map_err(|_| io::Error::from(io::ErrorKind::InvalidInput))?;
    let mut raw = RawStat::default();
    let r = unsafe { stat(c.as_ptr(), &mut raw) };
    if r < 0 { Err(io::Error::from(io::ErrorKind::NotFound)) } else { Ok(FileAttr(raw)) }
}

#[rustfmt::skip]
impl FileAttr {
    pub fn size(&self) -> u64             { self.0.st_size as u64 }
    pub fn perm(&self) -> FilePermissions { FilePermissions(self.0.st_mode) }
    pub fn file_type(&self) -> FileType   { FileType(self.0.st_mode) }
}
#[rustfmt::skip]
impl FilePermissions {
    pub fn readonly(&self) -> bool { (self.0 & 0o200) == 0 }
    pub fn set_readonly(&mut self, r: bool) {
        if r { self.0 &= !0o222 } else { self.0 |= 0o200 }
    }
}
#[rustfmt::skip]
impl FileType {
    pub fn is_dir(&self)     -> bool { (self.0 & 0o170000) == 0o040000 }
    pub fn is_file(&self)    -> bool { (self.0 & 0o170000) == 0o100000 }
    pub fn is_symlink(&self) -> bool { (self.0 & 0o170000) == 0o120000 }
}
#[rustfmt::skip]
impl Iterator for ReadDir {
    type Item = io::Result<DirEntry>;
    fn next(&mut self) -> Option<Self::Item> { None }
}
#[rustfmt::skip]
impl DirEntry {
    pub fn file_name(&self) -> OsString { OsString::new() }
    pub fn path(&self) -> PathBuf       { PathBuf::new() }
}
#[rustfmt::skip]
impl FromInner<i32> for File { fn from_inner(fd: i32) -> File { File(fd) } }

#[rustfmt::skip]
mod ops {
    use super::*;
    pub fn readdir(_p: &Path) -> io::Result<ReadDir>      { unsup() }
    pub fn unlink(_p: &Path) -> io::Result<()>            { unsup() }
    pub fn rename(_f: &Path, _t: &Path) -> io::Result<()> { unsup() }
    pub fn rmdir(_p: &Path) -> io::Result<()>             { unsup() }
    pub fn remove_dir_all(_p: &Path) -> io::Result<()>    { unsup() }
    pub fn readlink(_p: &Path) -> io::Result<PathBuf>     { unsup() }
    pub fn canonicalize(_p: &Path) -> io::Result<PathBuf> { unsup() }
}
pub use ops::*;
