use crate::error::CompileError;
use crate::value::Value;
use std::env;
use std::ffi::OsString;
use std::sync::atomic::{AtomicI64, Ordering};

const SEL_WINIT: i64 = 0;
const SEL_COCOA: i64 = 1;
const SEL_WIN32: i64 = 2;
const SEL_NONE: i64 = -1;

static SURFACE_OVERRIDE: AtomicI64 = AtomicI64::new(SEL_NONE);

fn classify_override(raw: &OsString) -> Option<i64> {
    let s = raw.to_string_lossy();
    match s.trim().to_ascii_lowercase().as_str() {
        "" => None,
        "winit" | "wayland" | "x11" | "default" | "auto" => Some(SEL_WINIT),
        "cocoa" | "macos" | "mac" | "osx" | "metal" => Some(SEL_COCOA),
        "win32" | "windows" | "win" | "gdi" => Some(SEL_WIN32),
        _ => None,
    }
}

fn host_default() -> i64 {
    if cfg!(target_os = "macos") {
        SEL_COCOA
    } else if cfg!(target_os = "windows") {
        SEL_WIN32
    } else {
        SEL_WINIT
    }
}

pub fn set_surface_override(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::semantic(format!(
            "rt_hosted_set_surface_override expects 1 argument, got {}",
            args.len()
        )));
    }
    let sel = match &args[0] {
        Value::Int(v) => *v,
        other => {
            return Err(CompileError::semantic(format!(
                "rt_hosted_set_surface_override expects int, got {}",
                other.type_name()
            )));
        }
    };
    SURFACE_OVERRIDE.store(sel, Ordering::Relaxed);
    Ok(Value::Nil)
}

pub fn select_surface(args: &[Value]) -> Result<Value, CompileError> {
    if !args.is_empty() {
        return Err(CompileError::semantic(format!(
            "rt_hosted_select_surface expects 0 arguments, got {}",
            args.len()
        )));
    }
    let prog = SURFACE_OVERRIDE.load(Ordering::Relaxed);
    if prog != SEL_NONE {
        return Ok(Value::Int(prog));
    }
    if let Some(raw) = env::var_os("SIMPLE_HOSTED_SURFACE") {
        if let Some(sel) = classify_override(&raw) {
            return Ok(Value::Int(sel));
        }
    }
    Ok(Value::Int(host_default()))
}
