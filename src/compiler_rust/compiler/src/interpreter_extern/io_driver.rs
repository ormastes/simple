use crate::error::CompileError;
use crate::value::Value;
use std::ffi::CString;

#[cfg(unix)]
extern "C" {
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

fn get_i64(args: &[Value], idx: usize) -> i64 {
    match &args[idx] {
        Value::Int(n) => *n,
        Value::Bool(b) => {
            if *b {
                1
            } else {
                0
            }
        }
        _ => 0,
    }
}

fn get_str_raw(args: &[Value], idx: usize) -> (*const i8, i64) {
    match &args[idx] {
        Value::Str(s) => (s.as_ptr() as *const i8, s.len() as i64),
        _ => (b"\0".as_ptr() as *const i8, 0),
    }
}

fn get_cstr(args: &[Value], idx: usize) -> CString {
    match &args[idx] {
        Value::Str(s) => CString::new(s.as_str()).unwrap_or_default(),
        _ => CString::default(),
    }
}

#[cfg(unix)]
pub fn dispatch(name: &str, args: &[Value]) -> Option<Result<Value, CompileError>> {
    let result = match name {
        "rt_driver_create" => Ok(Value::Int(unsafe { rt_driver_create(get_i64(args, 0)) })),
        "rt_driver_destroy" => {
            unsafe { rt_driver_destroy(get_i64(args, 0)) };
            Ok(Value::Nil)
        }
        "rt_driver_submit_accept" => Ok(Value::Int(unsafe {
            rt_driver_submit_accept(get_i64(args, 0), get_i64(args, 1))
        })),
        "rt_driver_submit_connect" => {
            let addr = get_cstr(args, 2);
            Ok(Value::Int(unsafe {
                rt_driver_submit_connect(get_i64(args, 0), get_i64(args, 1), addr.as_ptr(), get_i64(args, 3))
            }))
        }
        "rt_driver_submit_recv" => Ok(Value::Int(unsafe {
            rt_driver_submit_recv(get_i64(args, 0), get_i64(args, 1), get_i64(args, 2))
        })),
        "rt_driver_submit_send" => {
            let (ptr, _) = get_str_raw(args, 2);
            let len = get_i64(args, 3);
            Ok(Value::Int(unsafe {
                rt_driver_submit_send(get_i64(args, 0), get_i64(args, 1), ptr, len)
            }))
        }
        "rt_driver_submit_sendfile" => Ok(Value::Int(unsafe {
            rt_driver_submit_sendfile(
                get_i64(args, 0),
                get_i64(args, 1),
                get_i64(args, 2),
                get_i64(args, 3),
                get_i64(args, 4),
            )
        })),
        "rt_driver_submit_read" => Ok(Value::Int(unsafe {
            rt_driver_submit_read(get_i64(args, 0), get_i64(args, 1), get_i64(args, 2), get_i64(args, 3))
        })),
        "rt_driver_submit_write" => {
            let (ptr, _) = get_str_raw(args, 2);
            Ok(Value::Int(unsafe {
                rt_driver_submit_write(
                    get_i64(args, 0),
                    get_i64(args, 1),
                    ptr,
                    get_i64(args, 3),
                    get_i64(args, 4),
                )
            }))
        }
        "rt_driver_submit_open" => {
            let path = get_cstr(args, 1);
            Ok(Value::Int(unsafe {
                rt_driver_submit_open(get_i64(args, 0), path.as_ptr(), get_i64(args, 2), get_i64(args, 3))
            }))
        }
        "rt_driver_submit_close" => Ok(Value::Int(unsafe {
            rt_driver_submit_close(get_i64(args, 0), get_i64(args, 1))
        })),
        "rt_driver_submit_fsync" => Ok(Value::Int(unsafe {
            rt_driver_submit_fsync(get_i64(args, 0), get_i64(args, 1))
        })),
        "rt_driver_submit_timeout" => Ok(Value::Int(unsafe {
            rt_driver_submit_timeout(get_i64(args, 0), get_i64(args, 1))
        })),
        "rt_driver_flush" => Ok(Value::Int(unsafe { rt_driver_flush(get_i64(args, 0)) })),
        "rt_driver_poll" => Ok(Value::Int(unsafe {
            rt_driver_poll(get_i64(args, 0), get_i64(args, 1), get_i64(args, 2))
        })),
        "rt_driver_poll_id" => Ok(Value::Int(unsafe {
            rt_driver_poll_id(get_i64(args, 0), get_i64(args, 1))
        })),
        "rt_driver_poll_result" => Ok(Value::Int(unsafe {
            rt_driver_poll_result(get_i64(args, 0), get_i64(args, 1))
        })),
        "rt_driver_poll_flags" => Ok(Value::Int(unsafe {
            rt_driver_poll_flags(get_i64(args, 0), get_i64(args, 1))
        })),
        "rt_driver_poll_data" => {
            let handle = get_i64(args, 0);
            let index = get_i64(args, 1);
            unsafe {
                let ptr = rt_driver_poll_data(handle, index);
                let len = rt_driver_poll_data_len(handle, index);
                if ptr.is_null() || len <= 0 {
                    Ok(Value::Str("".into()))
                } else {
                    let slice = std::slice::from_raw_parts(ptr, len as usize);
                    Ok(Value::Str(String::from_utf8_lossy(slice).into_owned().into()))
                }
            }
        }
        "rt_driver_poll_data_len" => Ok(Value::Int(unsafe {
            rt_driver_poll_data_len(get_i64(args, 0), get_i64(args, 1))
        })),
        "rt_driver_cancel" => {
            let r = unsafe { rt_driver_cancel(get_i64(args, 0), get_i64(args, 1)) };
            Ok(Value::Bool(r))
        }
        "rt_driver_backend_name" => unsafe {
            let ptr = rt_driver_backend_name(get_i64(args, 0));
            if ptr.is_null() {
                Ok(Value::Str("unknown".into()))
            } else {
                let cstr = std::ffi::CStr::from_ptr(ptr as *const i8);
                Ok(Value::Str(cstr.to_string_lossy().into_owned().into()))
            }
        },
        "rt_driver_supports_sendfile" => Ok(Value::Bool(unsafe { rt_driver_supports_sendfile(get_i64(args, 0)) })),
        "rt_driver_supports_zero_copy" => Ok(Value::Bool(unsafe { rt_driver_supports_zero_copy(get_i64(args, 0)) })),
        _ => return None,
    };
    Some(result)
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
