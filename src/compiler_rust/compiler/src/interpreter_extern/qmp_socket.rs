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
