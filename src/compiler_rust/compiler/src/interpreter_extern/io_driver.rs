use crate::error::CompileError;
use crate::value::Value;
use std::ffi::CString;

#[cfg(unix)]
unsafe extern "C" {
    fn rt_driver_create(queue_depth: i64) -> i64;
    fn rt_driver_destroy(handle: i64);
    fn rt_driver_submit_accept(handle: i64, listen_fd: i64) -> i64;
    fn rt_driver_submit_connect(handle: i64, fd: i64, addr: *const i8, port: i64) -> i64;
    fn rt_driver_submit_recv(handle: i64, fd: i64, buf_size: i64) -> i64;
    fn rt_driver_submit_send(handle: i64, fd: i64, data: *const i8, len: i64) -> i64;
    fn rt_driver_submit_sendfile(handle: i64, sock_fd: i64, file_fd: i64, offset: i64, len: i64) -> i64;
    fn rt_driver_submit_read(handle: i64, fd: i64, buf_size: i64, offset: i64) -> i64;
    fn rt_driver_submit_write(handle: i64, fd: i64, data: *const i8, len: i64, offset: i64) -> i64;
    fn rt_driver_submit_open(handle: i64, path: *const i8, flags: i64, mode: i64) -> i64;
    fn rt_driver_submit_close(handle: i64, fd: i64) -> i64;
    fn rt_driver_submit_fsync(handle: i64, fd: i64) -> i64;
    fn rt_driver_submit_timeout(handle: i64, timeout_ms: i64) -> i64;
    fn rt_driver_flush(handle: i64) -> i64;
    fn rt_driver_poll(handle: i64, max: i64, timeout_ms: i64) -> i64;
    fn rt_driver_poll_id(handle: i64, index: i64) -> i64;
    fn rt_driver_poll_result(handle: i64, index: i64) -> i64;
    fn rt_driver_poll_flags(handle: i64, index: i64) -> i64;
    fn rt_driver_poll_data(handle: i64, index: i64) -> *const u8;
    fn rt_driver_poll_data_len(handle: i64, index: i64) -> i64;
    fn rt_driver_cancel(handle: i64, op_id: i64) -> bool;
    fn rt_driver_backend_name(handle: i64) -> *const u8;
    fn rt_driver_supports_sendfile(handle: i64) -> bool;
    fn rt_driver_supports_zero_copy(handle: i64) -> bool;
}

#[inline]
fn get_i64(args: &[Value], idx: usize, symbol: &str) -> Result<i64, CompileError> {
    match args.get(idx) {
        Some(Value::Int(value)) => Ok(*value),
        _ => Err(CompileError::runtime(format!(
            "{symbol}: argument {idx} must be an integer"
        ))),
    }
}

fn get_str<'a>(args: &'a [Value], idx: usize, symbol: &str) -> Result<&'a str, CompileError> {
    match args.get(idx) {
        Some(Value::Str(value)) => Ok(value.as_str()),
        _ => Err(CompileError::runtime(format!("{symbol}: argument {idx} must be text"))),
    }
}

fn get_cstr(args: &[Value], idx: usize, symbol: &str) -> Result<CString, CompileError> {
    CString::new(get_str(args, idx, symbol)?)
        .map_err(|_| CompileError::runtime(format!("{symbol}: argument {idx} contains an embedded NUL")))
}

fn checked_text_span<'a>(
    args: &'a [Value],
    text_index: usize,
    len_index: usize,
    symbol: &str,
) -> Result<(&'a str, i64), CompileError> {
    let text = get_str(args, text_index, symbol)?;
    let len = get_i64(args, len_index, symbol)?;
    if len < 0 || len as usize > text.len() {
        return Err(CompileError::runtime(format!(
            "{symbol}: length {len} exceeds text byte length {}",
            text.len()
        )));
    }
    Ok((text, len))
}

#[cfg(unix)]
pub fn dispatch(name: &str, args: &[Value]) -> Option<Result<Value, CompileError>> {
    match dispatch_checked(name, args) {
        Ok(Some(value)) => Some(Ok(value)),
        Ok(None) => None,
        Err(error) => Some(Err(error)),
    }
}

#[cfg(unix)]
#[inline]
fn dispatch_checked(name: &str, args: &[Value]) -> Result<Option<Value>, CompileError> {
    let result = match name {
        "rt_driver_create" => Ok(Value::Int(unsafe { rt_driver_create(get_i64(args, 0, name)?) })),
        "rt_driver_destroy" => {
            unsafe { rt_driver_destroy(get_i64(args, 0, name)?) };
            Ok(Value::Nil)
        }
        "rt_driver_submit_accept" => Ok(Value::Int(unsafe {
            rt_driver_submit_accept(get_i64(args, 0, name)?, get_i64(args, 1, name)?)
        })),
        "rt_driver_submit_connect" => {
            let addr = get_cstr(args, 2, name)?;
            Ok(Value::Int(unsafe {
                rt_driver_submit_connect(
                    get_i64(args, 0, name)?,
                    get_i64(args, 1, name)?,
                    addr.as_ptr().cast(),
                    get_i64(args, 3, name)?,
                )
            }))
        }
        "rt_driver_submit_recv" => Ok(Value::Int(unsafe {
            rt_driver_submit_recv(
                get_i64(args, 0, name)?,
                get_i64(args, 1, name)?,
                get_i64(args, 2, name)?,
            )
        })),
        "rt_driver_submit_send" => {
            let (data, len) = checked_text_span(args, 2, 3, name)?;
            Ok(Value::Int(unsafe {
                rt_driver_submit_send(
                    get_i64(args, 0, name)?,
                    get_i64(args, 1, name)?,
                    data.as_ptr().cast(),
                    len,
                )
            }))
        }
        "rt_driver_submit_sendfile" => Ok(Value::Int(unsafe {
            rt_driver_submit_sendfile(
                get_i64(args, 0, name)?,
                get_i64(args, 1, name)?,
                get_i64(args, 2, name)?,
                get_i64(args, 3, name)?,
                get_i64(args, 4, name)?,
            )
        })),
        "rt_driver_submit_read" => Ok(Value::Int(unsafe {
            rt_driver_submit_read(
                get_i64(args, 0, name)?,
                get_i64(args, 1, name)?,
                get_i64(args, 2, name)?,
                get_i64(args, 3, name)?,
            )
        })),
        "rt_driver_submit_write" => {
            let (data, len) = checked_text_span(args, 2, 3, name)?;
            Ok(Value::Int(unsafe {
                rt_driver_submit_write(
                    get_i64(args, 0, name)?,
                    get_i64(args, 1, name)?,
                    data.as_ptr().cast(),
                    len,
                    get_i64(args, 4, name)?,
                )
            }))
        }
        "rt_driver_submit_open" => {
            let path = get_cstr(args, 1, name)?;
            Ok(Value::Int(unsafe {
                rt_driver_submit_open(
                    get_i64(args, 0, name)?,
                    path.as_ptr().cast(),
                    get_i64(args, 2, name)?,
                    get_i64(args, 3, name)?,
                )
            }))
        }
        "rt_driver_submit_close" => Ok(Value::Int(unsafe {
            rt_driver_submit_close(get_i64(args, 0, name)?, get_i64(args, 1, name)?)
        })),
        "rt_driver_submit_fsync" => Ok(Value::Int(unsafe {
            rt_driver_submit_fsync(get_i64(args, 0, name)?, get_i64(args, 1, name)?)
        })),
        "rt_driver_submit_timeout" => Ok(Value::Int(unsafe {
            rt_driver_submit_timeout(get_i64(args, 0, name)?, get_i64(args, 1, name)?)
        })),
        "rt_driver_flush" => Ok(Value::Int(unsafe { rt_driver_flush(get_i64(args, 0, name)?) })),
        "rt_driver_poll" => Ok(Value::Int(unsafe {
            rt_driver_poll(
                get_i64(args, 0, name)?,
                get_i64(args, 1, name)?,
                get_i64(args, 2, name)?,
            )
        })),
        "rt_driver_poll_id" => Ok(Value::Int(unsafe {
            rt_driver_poll_id(get_i64(args, 0, name)?, get_i64(args, 1, name)?)
        })),
        "rt_driver_poll_result" => Ok(Value::Int(unsafe {
            rt_driver_poll_result(get_i64(args, 0, name)?, get_i64(args, 1, name)?)
        })),
        "rt_driver_poll_flags" => Ok(Value::Int(unsafe {
            rt_driver_poll_flags(get_i64(args, 0, name)?, get_i64(args, 1, name)?)
        })),
        "rt_driver_poll_data" => {
            let handle = get_i64(args, 0, name)?;
            let index = get_i64(args, 1, name)?;
            unsafe {
                let ptr = rt_driver_poll_data(handle, index);
                let len = rt_driver_poll_data_len(handle, index);
                if len < 0 || (ptr.is_null() && len > 0) {
                    Err(CompileError::runtime(format!(
                        "rt_driver_poll_data: invalid foreign data descriptor (null={}, len={len})",
                        ptr.is_null()
                    )))
                } else if len == 0 {
                    Ok(Value::text(""))
                } else {
                    let slice = std::slice::from_raw_parts(ptr, len as usize);
                    Ok(Value::text(String::from_utf8_lossy(slice).into_owned()))
                }
            }
        }
        "rt_driver_poll_data_len" => Ok(Value::Int(unsafe {
            rt_driver_poll_data_len(get_i64(args, 0, name)?, get_i64(args, 1, name)?)
        })),
        "rt_driver_cancel" => {
            let r = unsafe { rt_driver_cancel(get_i64(args, 0, name)?, get_i64(args, 1, name)?) };
            Ok(Value::Bool(r))
        }
        "rt_driver_backend_name" => unsafe {
            let ptr = rt_driver_backend_name(get_i64(args, 0, name)?);
            if ptr.is_null() {
                Err(CompileError::runtime(
                    "rt_driver_backend_name: provider returned null".to_string(),
                ))
            } else {
                let cstr = std::ffi::CStr::from_ptr(ptr as *const std::os::raw::c_char);
                Ok(Value::text(cstr.to_string_lossy().into_owned()))
            }
        },
        "rt_driver_supports_sendfile" => Ok(Value::Bool(unsafe {
            rt_driver_supports_sendfile(get_i64(args, 0, name)?)
        })),
        "rt_driver_supports_zero_copy" => Ok(Value::Bool(unsafe {
            rt_driver_supports_zero_copy(get_i64(args, 0, name)?)
        })),
        _ => return Ok(None),
    };
    Ok(Some(result?))
}

#[cfg(not(unix))]
pub fn dispatch(name: &str, _args: &[Value]) -> Option<Result<Value, CompileError>> {
    if name.starts_with("rt_driver_") {
        Some(Err(CompileError::runtime(
            "Async I/O driver not available on this platform",
        )))
    } else {
        None
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;

    fn is_dispatch_error(name: &str, args: &[Value]) -> bool {
        matches!(dispatch(name, args), Some(Err(_)))
    }

    #[test]
    fn driver_bridge_rejects_malformed_arguments_before_ffi() {
        assert!(is_dispatch_error("rt_driver_create", &[]));
        assert!(is_dispatch_error("rt_driver_destroy", &[Value::Bool(false)]));
        assert!(is_dispatch_error(
            "rt_driver_submit_connect",
            &[
                Value::Int(1),
                Value::Int(2),
                Value::text("bad\0address"),
                Value::Int(443),
            ],
        ));
        assert!(is_dispatch_error(
            "rt_driver_submit_send",
            &[Value::Int(1), Value::Int(2), Value::text("abc"), Value::Int(4),],
        ));
        assert!(is_dispatch_error(
            "rt_driver_submit_write",
            &[
                Value::Int(1),
                Value::Int(2),
                Value::text("abc"),
                Value::Int(-1),
                Value::Int(0),
            ],
        ));
        assert!(is_dispatch_error("rt_driver_poll", &[Value::Int(1)]));
        assert!(dispatch("rt_driver_unknown", &[]).is_none());
    }
}
