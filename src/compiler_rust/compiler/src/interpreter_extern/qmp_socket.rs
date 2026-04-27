//! QMP Unix-socket FFI for the interpreter
//!
//! Provides interpreter-mode implementations of the 4 rt_* primitives declared
//! in src/runtime/platform/unix_common.h and used by qmp_client.spl.
//!
//! On non-Unix platforms all functions return error/sentinel values.

use crate::error::CompileError;
use crate::value::Value;
use std::collections::HashMap;
use std::sync::Mutex;

// ── connection table ──────────────────────────────────────────────────────────

#[cfg(unix)]
use std::os::unix::net::UnixStream;
#[cfg(unix)]
use std::io::{Read, Write};

#[cfg(unix)]
struct ConnTable {
    next_fd: i64,
    streams: HashMap<i64, UnixStream>,
}

#[cfg(unix)]
impl ConnTable {
    fn new() -> Self {
        ConnTable {
            next_fd: 100,
            streams: HashMap::new(),
        }
    }
}

#[cfg(unix)]
static CONNS: Mutex<Option<ConnTable>> = Mutex::new(None);

// ── public extern handlers ────────────────────────────────────────────────────

/// `rt_unix_socket_connect(path: text) -> i64`
/// Returns a pseudo-fd (≥100) on success, -1 on failure.
pub fn rt_unix_socket_connect(args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(unix)]
    {
        let path = match args.first() {
            Some(Value::Str(s)) => s.clone(),
            _ => return Ok(Value::Int(-1)),
        };
        match UnixStream::connect(&path) {
            Ok(stream) => {
                let mut guard = CONNS.lock().unwrap();
                let table = guard.get_or_insert_with(ConnTable::new);
                let fd = table.next_fd;
                table.next_fd += 1;
                table.streams.insert(fd, stream);
                Ok(Value::Int(fd))
            }
            Err(_) => Ok(Value::Int(-1)),
        }
    }
    #[cfg(not(unix))]
    {
        let _ = args;
        Ok(Value::Int(-1))
    }
}

/// `rt_fd_write(fd: i64, data: text, len: i64) -> i64`
/// Returns bytes written, or -1 on error.
pub fn rt_fd_write(args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(unix)]
    {
        let fd = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Ok(Value::Int(-1)),
        };
        let data = match args.get(1) {
            Some(Value::Str(s)) => s.clone(),
            _ => return Ok(Value::Int(-1)),
        };
        let len = match args.get(2) {
            Some(Value::Int(n)) => *n as usize,
            _ => data.len(),
        };
        let bytes = &data.as_bytes()[..len.min(data.len())];

        let mut guard = CONNS.lock().unwrap();
        if let Some(table) = guard.as_mut() {
            if let Some(stream) = table.streams.get_mut(&fd) {
                return match stream.write_all(bytes) {
                    Ok(_) => Ok(Value::Int(bytes.len() as i64)),
                    Err(_) => Ok(Value::Int(-1)),
                };
            }
        }
        Ok(Value::Int(-1))
    }
    #[cfg(not(unix))]
    {
        let _ = args;
        Ok(Value::Int(-1))
    }
}

/// `rt_fd_read_until(fd: i64, stop_byte: i64, max: i64) -> text`
/// Reads bytes one-at-a-time until stop_byte or max bytes consumed.
pub fn rt_fd_read_until(args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(unix)]
    {
        let fd = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Ok(Value::Str(String::new())),
        };
        let stop = match args.get(1) {
            Some(Value::Int(n)) => *n as u8,
            _ => b'\n',
        };
        let max = match args.get(2) {
            Some(Value::Int(n)) => *n as usize,
            _ => 65536,
        };

        let mut guard = CONNS.lock().unwrap();
        if let Some(table) = guard.as_mut() {
            if let Some(stream) = table.streams.get_mut(&fd) {
                let mut buf = Vec::with_capacity(256);
                let mut byte = [0u8; 1];
                while buf.len() < max {
                    match stream.read_exact(&mut byte) {
                        Ok(_) => {
                            buf.push(byte[0]);
                            if byte[0] == stop {
                                break;
                            }
                        }
                        Err(_) => break,
                    }
                }
                return Ok(Value::Str(String::from_utf8_lossy(&buf).into_owned()));
            }
        }
        Ok(Value::Str(String::new()))
    }
    #[cfg(not(unix))]
    {
        let _ = args;
        Ok(Value::Str(String::new()))
    }
}

/// `rt_fd_close(fd: i64) -> bool`
pub fn rt_fd_close(args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(unix)]
    {
        let fd = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Ok(Value::Bool(false)),
        };
        let mut guard = CONNS.lock().unwrap();
        if let Some(table) = guard.as_mut() {
            if table.streams.remove(&fd).is_some() {
                return Ok(Value::Bool(true));
            }
        }
        Ok(Value::Bool(false))
    }
    #[cfg(not(unix))]
    {
        let _ = args;
        Ok(Value::Bool(false))
    }
}

// ── server-side UDS externs (SJ-UDS-001 / D-4 of jj-wrapper-daemon) ───────────
//
// Separate listener registry to leave the existing ConnTable untouched.
// Server-side accepted streams live in CONNS (reusing the same `streams`
// HashMap that the client side uses) so close/send/recv share a single fd
// pool. Listener fds live in LISTENERS keyed by the same next_fd counter.

#[cfg(unix)]
use std::os::unix::net::UnixListener;

#[cfg(unix)]
static LISTENERS: Mutex<Option<HashMap<i64, UnixListener>>> = Mutex::new(None);

const NEG_EAGAIN: i64 = -11;
const NEG_EBADF: i64 = -9;
const NEG_EINVAL: i64 = -22;
const NEG_EIO: i64 = -5;

/// `rt_unix_socket_listen(path: text, backlog: i32) -> i64`
pub fn rt_unix_socket_listen(args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(unix)]
    {
        let path = match args.first() {
            Some(Value::Str(s)) => s.clone(),
            _ => return Ok(Value::Int(NEG_EINVAL)),
        };
        if path.is_empty() {
            return Ok(Value::Int(NEG_EINVAL));
        }
        let _backlog = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => 16,
        };
        let _ = std::fs::remove_file(&path); // best-effort stale cleanup
        match UnixListener::bind(&path) {
            Ok(listener) => {
                if listener.set_nonblocking(true).is_err() {
                    return Ok(Value::Int(NEG_EIO));
                }
                let mut conns_guard = CONNS.lock().unwrap();
                let table = conns_guard.get_or_insert_with(ConnTable::new);
                let fd = table.next_fd;
                table.next_fd += 1;
                drop(conns_guard);
                let mut lguard = LISTENERS.lock().unwrap();
                lguard.get_or_insert_with(HashMap::new).insert(fd, listener);
                Ok(Value::Int(fd))
            }
            Err(_) => Ok(Value::Int(NEG_EIO)),
        }
    }
    #[cfg(not(unix))]
    { let _ = args; Ok(Value::Int(NEG_EIO)) }
}

/// `rt_unix_socket_accept(fd: i64) -> i64`
pub fn rt_unix_socket_accept(args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(unix)]
    {
        let fd = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Ok(Value::Int(NEG_EINVAL)),
        };
        let mut lguard = LISTENERS.lock().unwrap();
        let listener = match lguard.as_mut().and_then(|m| m.get(&fd)) {
            Some(l) => l,
            None => return Ok(Value::Int(NEG_EBADF)),
        };
        match listener.accept() {
            Ok((stream, _)) => {
                if stream.set_nonblocking(true).is_err() {
                    return Ok(Value::Int(NEG_EIO));
                }
                drop(lguard);
                let mut conns_guard = CONNS.lock().unwrap();
                let table = conns_guard.get_or_insert_with(ConnTable::new);
                let cfd = table.next_fd;
                table.next_fd += 1;
                table.streams.insert(cfd, stream);
                Ok(Value::Int(cfd))
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => Ok(Value::Int(NEG_EAGAIN)),
            Err(_) => Ok(Value::Int(NEG_EIO)),
        }
    }
    #[cfg(not(unix))]
    { let _ = args; Ok(Value::Int(NEG_EIO)) }
}

/// `rt_unix_socket_send(fd: i64, data: [u8]) -> i64`
/// Bytes are encoded as Value::Str (raw bytes, not UTF-8) — same convention as rt_fd_write.
pub fn rt_unix_socket_send(args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(unix)]
    {
        let fd = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Ok(Value::Int(NEG_EINVAL)),
        };
        let data = match args.get(1) {
            Some(Value::Str(s)) => s.clone(),
            _ => return Ok(Value::Int(NEG_EINVAL)),
        };
        let mut guard = CONNS.lock().unwrap();
        let table = match guard.as_mut() {
            Some(t) => t,
            None => return Ok(Value::Int(NEG_EBADF)),
        };
        let stream = match table.streams.get_mut(&fd) {
            Some(s) => s,
            None => return Ok(Value::Int(NEG_EBADF)),
        };
        match stream.write_all(data.as_bytes()) {
            Ok(_) => Ok(Value::Int(data.len() as i64)),
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => Ok(Value::Int(NEG_EAGAIN)),
            Err(_) => Ok(Value::Int(NEG_EIO)),
        }
    }
    #[cfg(not(unix))]
    { let _ = args; Ok(Value::Int(NEG_EIO)) }
}

/// `rt_unix_socket_recv(fd: i64, max_len: i64) -> [u8]`
/// Returns Value::Str (raw bytes; empty on EOF or EAGAIN or error).
pub fn rt_unix_socket_recv(args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(unix)]
    {
        let fd = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Ok(Value::Str(String::new())),
        };
        let max = match args.get(1) {
            Some(Value::Int(n)) => *n as usize,
            _ => 65536,
        };
        let mut guard = CONNS.lock().unwrap();
        let table = match guard.as_mut() {
            Some(t) => t,
            None => return Ok(Value::Str(String::new())),
        };
        let stream = match table.streams.get_mut(&fd) {
            Some(s) => s,
            None => return Ok(Value::Str(String::new())),
        };
        let mut buf = vec![0u8; max];
        match stream.read(&mut buf) {
            Ok(n) => {
                buf.truncate(n);
                Ok(Value::Str(String::from_utf8_lossy(&buf).into_owned()))
            }
            Err(_) => Ok(Value::Str(String::new())),
        }
    }
    #[cfg(not(unix))]
    { let _ = args; Ok(Value::Str(String::new())) }
}

/// `rt_unix_socket_close(fd: i64) -> i32`
/// Returns 0 on success, NEG_EBADF if fd unknown.
pub fn rt_unix_socket_close(args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(unix)]
    {
        let fd = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Ok(Value::Int(NEG_EINVAL)),
        };
        // Try listener registry first.
        let mut lguard = LISTENERS.lock().unwrap();
        if let Some(map) = lguard.as_mut() {
            if map.remove(&fd).is_some() {
                return Ok(Value::Int(0));
            }
        }
        drop(lguard);
        // Then stream registry.
        let mut guard = CONNS.lock().unwrap();
        if let Some(table) = guard.as_mut() {
            if table.streams.remove(&fd).is_some() {
                return Ok(Value::Int(0));
            }
        }
        Ok(Value::Int(NEG_EBADF))
    }
    #[cfg(not(unix))]
    { let _ = args; Ok(Value::Int(NEG_EBADF)) }
}
