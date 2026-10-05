//! Unix interpreter providers for the snapshot owner's no-follow operations.
use crate::{error::CompileError, value::Value};
use std::ffi::CString;
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};

fn text(args: &[Value], index: usize) -> Option<&str> {
    let Value::Str(value) = args.get(index)? else { return None; };
    let value = value.as_str();
    (!value.is_empty() && value.len() < 4096 && !value.as_bytes().contains(&0)).then_some(value)
}
fn kind(args: &[Value], index: usize) -> Option<i64> {
    match args.get(index) { Some(Value::Int(value @ (1 | 2))) => Some(*value), _ => None }
}
fn absolute(path: &str) -> bool {
    path.len() >= 2 && path.len() < 4096 && path.starts_with('/') && !path.ends_with('/')
        && !path.contains('\\') && !path.as_bytes().contains(&0)
        && path[1..].split('/').all(|part| !matches!(part, "" | "." | ".."))
}
fn resolved(root: &str, link: &str, target: &str) -> Option<String> {
    if !absolute(root) || !absolute(link) || !link.starts_with(&format!("{root}/"))
        || target.starts_with('/') || target.ends_with('/') || target.contains(['\\', ':']) {
        return None;
    }
    let (parent, _) = link.rsplit_once('/')?;
    let mut result = parent.to_owned();
    for part in target.split('/') {
        match part {
            "" => return None,
            "." => {},
            ".." => {
                if result.len() <= root.len() { return None; }
                result.truncate(result.rfind('/')?);
                if result.len() < root.len() { return None; }
            },
            name => { result.push('/'); result.push_str(name); },
        }
    }
    absolute(&result).then_some(result)
}
fn parent(path: &str) -> Option<(OwnedFd, CString)> {
    if !absolute(path) { return None; }
    let (directory, leaf) = path.rsplit_once('/')?;
    let fd = super::file_io::safe_artifact_open_root(if directory.is_empty() { "/" } else { directory })?;
    let owner = unsafe { OwnedFd::from_raw_fd(fd) };
    Some((owner, CString::new(leaf).ok()?))
}
fn has_kind(path: &str, kind: i64) -> bool {
    let Some((directory, leaf)) = parent(path) else { return false; };
    let mut info: libc::stat = unsafe { std::mem::zeroed() };
    (unsafe { libc::fstatat(directory.as_raw_fd(), leaf.as_ptr(), &mut info, libc::AT_SYMLINK_NOFOLLOW) == 0 })
        && info.st_mode & libc::S_IFMT == if kind == 1 { libc::S_IFREG } else { libc::S_IFDIR }
}
fn exact_link(link: &str, target: &str) -> bool {
    let Some((directory, leaf)) = parent(link) else { return false; };
    let mut info: libc::stat = unsafe { std::mem::zeroed() };
    if unsafe { libc::fstatat(directory.as_raw_fd(), leaf.as_ptr(), &mut info, libc::AT_SYMLINK_NOFOLLOW) } != 0
        || info.st_mode & libc::S_IFMT != libc::S_IFLNK { return false; }
    let mut raw = [0u8; 4096];
    let length = unsafe { libc::readlinkat(directory.as_raw_fd(), leaf.as_ptr(), raw.as_mut_ptr().cast(), raw.len()) };
    length >= 0 && length as usize == target.len() && &raw[..length as usize] == target.as_bytes()
}
fn link_args(args: &[Value]) -> Option<(&str, &str, &str, i64, String)> {
    let (root, link, target, kind) = (text(args, 0)?, text(args, 1)?, text(args, 2)?, kind(args, 3)?);
    let resolved = resolved(root, link, target)?;
    Some((root, link, target, kind, resolved))
}
pub fn matches(args: &[Value]) -> Result<Value, CompileError> {
    let ok = link_args(args).is_some_and(|(_, link, target, kind, resolved)|
        has_kind(&resolved, kind) && exact_link(link, target));
    Ok(Value::Int(if ok { 0 } else { -1 }))
}
pub fn create(args: &[Value]) -> Result<Value, CompileError> {
    let Some((_, link, target, kind, resolved)) = link_args(args) else { return Ok(Value::Int(-1)); };
    if !has_kind(&resolved, kind) { return Ok(Value::Int(-1)); }
    let Some((directory, leaf)) = parent(link) else { return Ok(Value::Int(-1)); };
    let target_c = CString::new(target).expect("validated target has no NUL");
    if unsafe { libc::symlinkat(target_c.as_ptr(), directory.as_raw_fd(), leaf.as_ptr()) } != 0 {
        return Ok(Value::Int(-1));
    }
    matches(args)
}
pub fn readonly(args: &[Value]) -> Result<Value, CompileError> {
    let Some(path) = text(args, 0) else { return Ok(Value::Int(-1)); };
    let Some(kind) = kind(args, 1) else { return Ok(Value::Int(-1)); };
    let Some((directory, leaf)) = parent(path) else { return Ok(Value::Int(-1)); };
    let flags = libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK
        | if kind == 2 { libc::O_DIRECTORY } else { 0 };
    let fd = unsafe { libc::openat(directory.as_raw_fd(), leaf.as_ptr(), flags) };
    if fd < 0 { return Ok(Value::Int(-1)); }
    let fd = unsafe { OwnedFd::from_raw_fd(fd) };
    let mut before: libc::stat = unsafe { std::mem::zeroed() };
    if unsafe { libc::fstat(fd.as_raw_fd(), &mut before) } != 0
        || before.st_mode & libc::S_IFMT != if kind == 1 { libc::S_IFREG } else { libc::S_IFDIR } {
        return Ok(Value::Int(-1));
    }
    let desired = before.st_mode & 0o7777 & !0o222;
    let mut after: libc::stat = unsafe { std::mem::zeroed() };
    let ok = unsafe { libc::fchmod(fd.as_raw_fd(), desired) == 0
        && libc::fstat(fd.as_raw_fd(), &mut after) == 0 } && after.st_mode & 0o222 == 0;
    Ok(Value::Int(if ok { 0 } else { -1 }))
}
