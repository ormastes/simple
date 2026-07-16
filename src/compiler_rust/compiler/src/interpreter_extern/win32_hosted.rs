use crate::error::CompileError;
use crate::value::Value;

fn int_arg(args: &[Value], idx: usize, name: &str) -> Result<i64, CompileError> {
    match args.get(idx) {
        Some(Value::Int(v)) => Ok(*v),
        other => Err(CompileError::semantic(format!(
            "{name} argument {idx} must be i64, got {}",
            other.map(|v| v.type_name()).unwrap_or("missing")
        ))),
    }
}

fn text_arg(args: &[Value], idx: usize, name: &str) -> Result<String, CompileError> {
    match args.get(idx) {
        Some(Value::Str(v)) => Ok(v.as_ref().clone()),
        other => Err(CompileError::semantic(format!(
            "{name} argument {idx} must be text, got {}",
            other.map(|v| v.type_name()).unwrap_or("missing")
        ))),
    }
}

#[cfg(target_os = "windows")]
fn with_c_string<T>(value: String, fallback: T, f: impl FnOnce(*const std::ffi::c_char) -> T) -> T {
    match std::ffi::CString::new(value) {
        Ok(c) => f(c.as_ptr()),
        Err(_) => fallback,
    }
}

pub fn rt_win32_window_new(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 3 {
        return Err(CompileError::semantic("rt_win32_window_new expects 3 arguments"));
    }
    let w = int_arg(args, 0, "rt_win32_window_new")?;
    let h = int_arg(args, 1, "rt_win32_window_new")?;
    let title = text_arg(args, 2, "rt_win32_window_new")?;
    #[cfg(target_os = "windows")]
    {
        let handle = with_c_string(title, -1, |ptr| unsafe {
            spl_hosted_runtime::win32::rt_win32_window_new(w, h, ptr)
        });
        Ok(Value::Int(handle))
    }
    #[cfg(not(target_os = "windows"))]
    {
        let _ = title;
        Ok(Value::Int(-1))
    }
}

pub fn rt_win32_window_close(args: &[Value]) -> Result<Value, CompileError> {
    let hwnd = int_arg(args, 0, "rt_win32_window_close")?;
    #[cfg(target_os = "windows")]
    {
        Ok(Value::Bool(unsafe { spl_hosted_runtime::win32::rt_win32_window_close(hwnd) }))
    }
    #[cfg(not(target_os = "windows"))]
    {
        let _ = hwnd;
        Ok(Value::Bool(false))
    }
}

pub fn rt_win32_dib_create(args: &[Value]) -> Result<Value, CompileError> {
    let hwnd = int_arg(args, 0, "rt_win32_dib_create")?;
    let w = int_arg(args, 1, "rt_win32_dib_create")?;
    let h = int_arg(args, 2, "rt_win32_dib_create")?;
    let fill = int_arg(args, 3, "rt_win32_dib_create")?;
    #[cfg(target_os = "windows")]
    {
        Ok(Value::Int(unsafe {
            spl_hosted_runtime::win32::rt_win32_dib_create(hwnd, w, h, fill)
        }))
    }
    #[cfg(not(target_os = "windows"))]
    {
        let _ = (hwnd, w, h, fill);
        Ok(Value::Int(-1))
    }
}

pub fn rt_win32_dib_fill_rect(args: &[Value]) -> Result<Value, CompileError> {
    let dib = int_arg(args, 0, "rt_win32_dib_fill_rect")?;
    let x = int_arg(args, 1, "rt_win32_dib_fill_rect")?;
    let y = int_arg(args, 2, "rt_win32_dib_fill_rect")?;
    let w = int_arg(args, 3, "rt_win32_dib_fill_rect")?;
    let h = int_arg(args, 4, "rt_win32_dib_fill_rect")?;
    let color = int_arg(args, 5, "rt_win32_dib_fill_rect")?;
    #[cfg(target_os = "windows")]
    {
        Ok(Value::Bool(unsafe {
            spl_hosted_runtime::win32::rt_win32_dib_fill_rect(dib, x, y, w, h, color)
        }))
    }
    #[cfg(not(target_os = "windows"))]
    {
        let _ = (dib, x, y, w, h, color);
        Ok(Value::Bool(false))
    }
}

pub fn rt_win32_dib_present(args: &[Value]) -> Result<Value, CompileError> {
    let hwnd = int_arg(args, 0, "rt_win32_dib_present")?;
    let dib = int_arg(args, 1, "rt_win32_dib_present")?;
    #[cfg(target_os = "windows")]
    {
        Ok(Value::Bool(unsafe { spl_hosted_runtime::win32::rt_win32_dib_present(hwnd, dib) }))
    }
    #[cfg(not(target_os = "windows"))]
    {
        let _ = (hwnd, dib);
        Ok(Value::Bool(false))
    }
}

pub fn rt_win32_dib_free(args: &[Value]) -> Result<Value, CompileError> {
    let dib = int_arg(args, 0, "rt_win32_dib_free")?;
    #[cfg(target_os = "windows")]
    {
        Ok(Value::Bool(unsafe { spl_hosted_runtime::win32::rt_win32_dib_free(dib) }))
    }
    #[cfg(not(target_os = "windows"))]
    {
        let _ = dib;
        Ok(Value::Bool(false))
    }
}

pub fn rt_win32_dib_read_pixel(args: &[Value]) -> Result<Value, CompileError> {
    let dib = int_arg(args, 0, "rt_win32_dib_read_pixel")?;
    let x = int_arg(args, 1, "rt_win32_dib_read_pixel")?;
    let y = int_arg(args, 2, "rt_win32_dib_read_pixel")?;
    #[cfg(target_os = "windows")]
    {
        Ok(Value::Int(unsafe {
            spl_hosted_runtime::win32::rt_win32_dib_read_pixel(dib, x, y)
        }))
    }
    #[cfg(not(target_os = "windows"))]
    {
        let _ = (dib, x, y);
        Ok(Value::Int(0))
    }
}

pub fn rt_win32_message_pump(args: &[Value]) -> Result<Value, CompileError> {
    let hwnd = int_arg(args, 0, "rt_win32_message_pump")?;
    #[cfg(target_os = "windows")]
    {
        Ok(Value::Int(unsafe { spl_hosted_runtime::win32::rt_win32_message_pump(hwnd) }))
    }
    #[cfg(not(target_os = "windows"))]
    {
        let _ = hwnd;
        Ok(Value::Int(0))
    }
}
