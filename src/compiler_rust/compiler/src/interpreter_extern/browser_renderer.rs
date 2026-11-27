//! Seed-interpreter registrations for the `rt_browser_renderer_*` family.
//!
//! Mirrors the C runtime's non-Linux semantics (`runtime_process.c`):
//! the namespace sandbox is not available in the seed, so spawning is refused
//! (`-1`, never an unsandboxed spawn), `sandbox_enter`/`netns_active` report
//! `false`, the protocol channel write is refused (`-1`), and the stdin/stdout
//! helpers perform real bounded I/O on the process's own handles.

use crate::error::CompileError;
use crate::value::Value;
use std::io::{Read, Write};

const WRITE_CAP: i64 = 1_048_576;
const READ_CAP: i64 = 65_535;

fn int_arg(args: &[Value], idx: usize, symbol: &str) -> Result<i64, CompileError> {
    match args.get(idx) {
        Some(Value::Int(v)) => Ok(*v),
        Some(Value::UInt { value, .. }) => Ok(*value as i64),
        _ => Err(CompileError::runtime(format!("{symbol}: argument {idx} must be an integer"))),
    }
}

/// `rt_browser_renderer_spawn_sandboxed(cmd, args) -> i64`: sandbox unavailable => -1.
pub fn rt_browser_renderer_spawn_sandboxed(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::semantic(
            "rt_browser_renderer_spawn_sandboxed() expects 2 arguments (cmd: text, args: [text])",
        ));
    }
    Ok(Value::Int(-1))
}

/// `rt_browser_renderer_sandbox_enter() -> bool`: no sandbox layer in the seed.
pub fn rt_browser_renderer_sandbox_enter(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(false))
}

/// `rt_browser_renderer_sandbox_netns_active() -> bool`.
pub fn rt_browser_renderer_sandbox_netns_active(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(false))
}

/// `rt_browser_renderer_namespaces_active() -> bool`.
pub fn rt_browser_renderer_namespaces_active(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(false))
}

/// `rt_browser_renderer_read_stdin_some(max_bytes) -> text`: one bounded read, "" on EOF/error.
pub fn rt_browser_renderer_read_stdin_some(args: &[Value]) -> Result<Value, CompileError> {
    let max = int_arg(args, 0, "rt_browser_renderer_read_stdin_some")?;
    if max <= 0 {
        return Ok(Value::text(String::new()));
    }
    let want = max.min(READ_CAP) as usize;
    let mut buf = vec![0u8; want];
    let n = std::io::stdin().lock().read(&mut buf).unwrap_or(0);
    buf.truncate(n);
    Ok(Value::text(String::from_utf8_lossy(&buf).into_owned()))
}

/// `rt_browser_renderer_write_stdout_some(data, data_len, offset, max_bytes) -> i64`.
pub fn rt_browser_renderer_write_stdout_some(args: &[Value]) -> Result<Value, CompileError> {
    let sym = "rt_browser_renderer_write_stdout_some";
    let data = match args.first() {
        Some(Value::Str(s)) => s.as_bytes().to_vec(),
        _ => return Err(CompileError::runtime(format!("{sym}: argument 0 must be text"))),
    };
    let data_len = int_arg(args, 1, sym)?;
    let offset = int_arg(args, 2, sym)?;
    let max = int_arg(args, 3, sym)?;
    if data_len < 0 || offset < 0 || offset > data_len || max <= 0 || data_len as usize > data.len() {
        return Ok(Value::Int(-1));
    }
    if offset == data_len {
        return Ok(Value::Int(0));
    }
    let count = (data_len - offset).min(max.min(WRITE_CAP)) as usize;
    let start = offset as usize;
    let mut out = std::io::stdout().lock();
    match out.write_all(&data[start..start + count]).and_then(|_| out.flush()) {
        Ok(()) => Ok(Value::Int(count as i64)),
        Err(_) => Ok(Value::Int(-1)),
    }
}

/// `rt_browser_renderer_write_protocol_some(...) -> i64`: no protocol channel => -1.
pub fn rt_browser_renderer_write_protocol_some(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(-1))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spawn_is_refused_when_no_sandbox_exists() {
        let args = [Value::text("cmd"), Value::Nil];
        assert_eq!(rt_browser_renderer_spawn_sandboxed(&args).unwrap(), Value::Int(-1));
        assert_eq!(rt_browser_renderer_sandbox_enter(&[]).unwrap(), Value::Bool(false));
        assert_eq!(rt_browser_renderer_sandbox_netns_active(&[]).unwrap(), Value::Bool(false));
        assert_eq!(rt_browser_renderer_write_protocol_some(&[]).unwrap(), Value::Int(-1));
    }

    #[test]
    fn write_stdout_validates_bounds() {
        let t = |d: &str, len, off, max| {
            rt_browser_renderer_write_stdout_some(&[Value::text(d), Value::Int(len), Value::Int(off), Value::Int(max)]).unwrap()
        };
        assert_eq!(t("abc", 3, 4, 8), Value::Int(-1));
        assert_eq!(t("abc", 3, 0, 0), Value::Int(-1));
        assert_eq!(t("abc", 3, 3, 8), Value::Int(0));
        assert_eq!(t("abc", 9, 0, 8), Value::Int(-1));
    }
}
