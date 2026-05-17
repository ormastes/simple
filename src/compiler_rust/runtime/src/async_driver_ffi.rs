use std::io;
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

use crate::value::{rt_string_new, RuntimeValue};

#[derive(Clone)]
struct Completion {
    id: i64,
    result: i64,
    flags: i64,
    data: Vec<u8>,
}

enum Operation {
    Accept {
        id: i64,
        listen_fd: i64,
    },
    Recv {
        id: i64,
        fd: i64,
        size: i64,
    },
    Send {
        id: i64,
        fd: i64,
        data: Vec<u8>,
    },
    Sendfile {
        id: i64,
        sock_fd: i64,
        file_fd: i64,
        offset: i64,
        len: i64,
    },
    Read {
        id: i64,
        fd: i64,
        size: i64,
        offset: i64,
    },
    Write {
        id: i64,
        fd: i64,
        data: Vec<u8>,
        offset: i64,
    },
    Open {
        id: i64,
        path: String,
        flags: i64,
        mode: i64,
    },
    Close {
        id: i64,
        fd: i64,
    },
    Fsync {
        id: i64,
        fd: i64,
    },
    Timeout {
        id: i64,
        timeout_ms: i64,
    },
}

struct Driver {
    next_id: i64,
    queue: Vec<Operation>,
    completions: Vec<Completion>,
    poll_snapshot: Vec<Completion>,
}

impl Driver {
    fn new(queue_depth: i64) -> Self {
        let capacity = queue_depth.clamp(16, 65_536) as usize;
        Self {
            next_id: 1,
            queue: Vec::with_capacity(capacity),
            completions: Vec::with_capacity(capacity.min(1024)),
            poll_snapshot: Vec::with_capacity(capacity.min(1024)),
        }
    }

    fn alloc_id(&mut self) -> i64 {
        let id = self.next_id;
        self.next_id = self.next_id.saturating_add(1).max(1);
        id
    }

    fn submit(&mut self, operation: Operation) -> i64 {
        let id = operation_id(&operation);
        self.queue.push(operation);
        id
    }
}

fn operation_id(operation: &Operation) -> i64 {
    match operation {
        Operation::Accept { id, .. }
        | Operation::Recv { id, .. }
        | Operation::Send { id, .. }
        | Operation::Sendfile { id, .. }
        | Operation::Read { id, .. }
        | Operation::Write { id, .. }
        | Operation::Open { id, .. }
        | Operation::Close { id, .. }
        | Operation::Fsync { id, .. }
        | Operation::Timeout { id, .. } => *id,
    }
}

fn drivers() -> &'static Mutex<Vec<Option<Driver>>> {
    static DRIVERS: OnceLock<Mutex<Vec<Option<Driver>>>> = OnceLock::new();
    DRIVERS.get_or_init(|| Mutex::new(Vec::new()))
}

fn with_driver_mut<R>(handle: i64, f: impl FnOnce(&mut Driver) -> R) -> Option<R> {
    let mut guard = drivers().lock().ok()?;
    let driver = guard.get_mut(handle as usize)?.as_mut()?;
    Some(f(driver))
}

fn os_error_code() -> i64 {
    -(io::Error::last_os_error().raw_os_error().unwrap_or(libc::EIO) as i64)
}

unsafe fn bytes_from_raw<'a>(ptr: *const u8, len: i64) -> Option<&'a [u8]> {
    if len < 0 || (ptr.is_null() && len > 0) {
        return None;
    }
    Some(std::slice::from_raw_parts(ptr, len as usize))
}

fn completion(id: i64, result: i64) -> Completion {
    Completion {
        id,
        result,
        flags: 0,
        data: Vec::new(),
    }
}

fn data_completion(id: i64, result: i64, data: Vec<u8>) -> Completion {
    Completion {
        id,
        result,
        flags: 0,
        data,
    }
}

fn execute_operation(operation: Operation) -> Completion {
    match operation {
        Operation::Accept { id, listen_fd } => {
            let accepted =
                unsafe { libc::accept(listen_fd as libc::c_int, std::ptr::null_mut(), std::ptr::null_mut()) };
            completion(id, if accepted < 0 { os_error_code() } else { accepted as i64 })
        }
        Operation::Recv { id, fd, size } => {
            let mut data = vec![0_u8; size.max(0) as usize];
            let n = unsafe { libc::recv(fd as libc::c_int, data.as_mut_ptr() as *mut libc::c_void, data.len(), 0) };
            if n < 0 {
                completion(id, os_error_code())
            } else {
                data.truncate(n as usize);
                data_completion(id, n as i64, data)
            }
        }
        Operation::Send { id, fd, data } => {
            let n = unsafe {
                libc::send(
                    fd as libc::c_int,
                    data.as_ptr() as *const libc::c_void,
                    data.len(),
                    libc::MSG_NOSIGNAL,
                )
            };
            completion(id, if n < 0 { os_error_code() } else { n as i64 })
        }
        Operation::Sendfile {
            id,
            sock_fd,
            file_fd,
            mut offset,
            len,
        } => {
            #[cfg(target_os = "linux")]
            let n = unsafe {
                libc::sendfile(
                    sock_fd as libc::c_int,
                    file_fd as libc::c_int,
                    &mut offset as *mut i64 as *mut libc::off_t,
                    len.max(0) as usize,
                )
            };
            #[cfg(not(target_os = "linux"))]
            let n = -1;
            completion(id, if n < 0 { os_error_code() } else { n as i64 })
        }
        Operation::Read { id, fd, size, offset } => {
            let mut data = vec![0_u8; size.max(0) as usize];
            let n = unsafe {
                libc::pread(
                    fd as libc::c_int,
                    data.as_mut_ptr() as *mut libc::c_void,
                    data.len(),
                    offset as libc::off_t,
                )
            };
            if n < 0 {
                completion(id, os_error_code())
            } else {
                data.truncate(n as usize);
                data_completion(id, n as i64, data)
            }
        }
        Operation::Write { id, fd, data, offset } => {
            let n = unsafe {
                libc::pwrite(
                    fd as libc::c_int,
                    data.as_ptr() as *const libc::c_void,
                    data.len(),
                    offset as libc::off_t,
                )
            };
            completion(id, if n < 0 { os_error_code() } else { n as i64 })
        }
        Operation::Open { id, path, flags, mode } => {
            let Ok(c_path) = std::ffi::CString::new(path) else {
                return completion(id, -(libc::EINVAL as i64));
            };
            let fd = unsafe { libc::open(c_path.as_ptr(), flags as libc::c_int, mode as libc::mode_t) };
            completion(id, if fd < 0 { os_error_code() } else { fd as i64 })
        }
        Operation::Close { id, fd } => {
            let result = unsafe { libc::close(fd as libc::c_int) };
            completion(id, if result < 0 { os_error_code() } else { 0 })
        }
        Operation::Fsync { id, fd } => {
            let result = unsafe { libc::fsync(fd as libc::c_int) };
            completion(id, if result < 0 { os_error_code() } else { 0 })
        }
        Operation::Timeout { id, timeout_ms } => {
            if timeout_ms > 0 {
                std::thread::sleep(Duration::from_millis(timeout_ms as u64));
            }
            completion(id, 0)
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_driver_create(queue_depth: i64) -> i64 {
    let mut guard = match drivers().lock() {
        Ok(guard) => guard,
        Err(_) => return -1,
    };
    if let Some((index, slot)) = guard.iter_mut().enumerate().find(|(_, slot)| slot.is_none()) {
        *slot = Some(Driver::new(queue_depth));
        return index as i64;
    }
    guard.push(Some(Driver::new(queue_depth)));
    (guard.len() - 1) as i64
}

#[no_mangle]
pub extern "C" fn rt_driver_destroy(handle: i64) {
    if let Ok(mut guard) = drivers().lock() {
        if let Some(slot) = guard.get_mut(handle as usize) {
            *slot = None;
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_driver_submit_accept(handle: i64, listen_fd: i64) -> i64 {
    with_driver_mut(handle, |driver| {
        let id = driver.alloc_id();
        driver.submit(Operation::Accept { id, listen_fd })
    })
    .unwrap_or(-1)
}

#[no_mangle]
pub unsafe extern "C" fn rt_driver_submit_connect(
    _handle: i64,
    _fd: i64,
    _addr: *const u8,
    _addr_len: i64,
    _port: i64,
) -> i64 {
    -(libc::ENOSYS as i64)
}

#[no_mangle]
pub extern "C" fn rt_driver_submit_recv(handle: i64, fd: i64, buf_size: i64) -> i64 {
    with_driver_mut(handle, |driver| {
        let id = driver.alloc_id();
        driver.submit(Operation::Recv { id, fd, size: buf_size })
    })
    .unwrap_or(-1)
}

#[no_mangle]
pub unsafe extern "C" fn rt_driver_submit_send(handle: i64, fd: i64, data: *const u8, len: i64) -> i64 {
    let Some(bytes) = bytes_from_raw(data, len) else {
        return -1;
    };
    with_driver_mut(handle, |driver| {
        let id = driver.alloc_id();
        driver.submit(Operation::Send {
            id,
            fd,
            data: bytes.to_vec(),
        })
    })
    .unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn rt_driver_submit_sendfile(handle: i64, sock_fd: i64, file_fd: i64, offset: i64, len: i64) -> i64 {
    with_driver_mut(handle, |driver| {
        let id = driver.alloc_id();
        driver.submit(Operation::Sendfile {
            id,
            sock_fd,
            file_fd,
            offset,
            len,
        })
    })
    .unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn rt_driver_submit_read(handle: i64, fd: i64, buf_size: i64, offset: i64) -> i64 {
    with_driver_mut(handle, |driver| {
        let id = driver.alloc_id();
        driver.submit(Operation::Read {
            id,
            fd,
            size: buf_size,
            offset,
        })
    })
    .unwrap_or(-1)
}

#[no_mangle]
pub unsafe extern "C" fn rt_driver_submit_write(handle: i64, fd: i64, data: *const u8, len: i64, offset: i64) -> i64 {
    let Some(bytes) = bytes_from_raw(data, len) else {
        return -1;
    };
    with_driver_mut(handle, |driver| {
        let id = driver.alloc_id();
        driver.submit(Operation::Write {
            id,
            fd,
            data: bytes.to_vec(),
            offset,
        })
    })
    .unwrap_or(-1)
}

#[no_mangle]
pub unsafe extern "C" fn rt_driver_submit_open(
    handle: i64,
    path: *const u8,
    path_len: i64,
    flags: i64,
    mode: i64,
) -> i64 {
    let Some(bytes) = bytes_from_raw(path, path_len) else {
        return -1;
    };
    let path = match std::str::from_utf8(bytes) {
        Ok(path) => path.to_string(),
        Err(_) => return -1,
    };
    with_driver_mut(handle, |driver| {
        let id = driver.alloc_id();
        driver.submit(Operation::Open { id, path, flags, mode })
    })
    .unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn rt_driver_submit_close(handle: i64, fd: i64) -> i64 {
    with_driver_mut(handle, |driver| {
        let id = driver.alloc_id();
        driver.submit(Operation::Close { id, fd })
    })
    .unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn rt_driver_submit_fsync(handle: i64, fd: i64) -> i64 {
    with_driver_mut(handle, |driver| {
        let id = driver.alloc_id();
        driver.submit(Operation::Fsync { id, fd })
    })
    .unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn rt_driver_submit_timeout(handle: i64, timeout_ms: i64) -> i64 {
    with_driver_mut(handle, |driver| {
        let id = driver.alloc_id();
        driver.submit(Operation::Timeout { id, timeout_ms })
    })
    .unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn rt_driver_flush(handle: i64) -> i64 {
    with_driver_mut(handle, |driver| {
        let queued: Vec<_> = driver.queue.drain(..).collect();
        let count = queued.len() as i64;
        driver.completions.extend(queued.into_iter().map(execute_operation));
        count
    })
    .unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn rt_driver_poll(handle: i64, max: i64, timeout_ms: i64) -> i64 {
    with_driver_mut(handle, |driver| {
        let limit = max.clamp(0, 4096) as usize;
        let deadline = if timeout_ms > 0 {
            Some(Instant::now() + Duration::from_millis(timeout_ms as u64))
        } else {
            None
        };
        while driver.completions.is_empty() && timeout_ms != 0 {
            if let Some(deadline) = deadline {
                if Instant::now() >= deadline {
                    break;
                }
            }
            std::thread::sleep(Duration::from_millis(1));
        }
        let count = limit.min(driver.completions.len());
        driver.poll_snapshot = driver.completions.drain(0..count).collect();
        count as i64
    })
    .unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn rt_driver_poll_id(handle: i64, index: i64) -> i64 {
    with_driver_mut(handle, |driver| {
        driver.poll_snapshot.get(index as usize).map(|c| c.id).unwrap_or(-1)
    })
    .unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn rt_driver_poll_result(handle: i64, index: i64) -> i64 {
    with_driver_mut(handle, |driver| {
        driver.poll_snapshot.get(index as usize).map(|c| c.result).unwrap_or(-1)
    })
    .unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn rt_driver_poll_flags(handle: i64, index: i64) -> i64 {
    with_driver_mut(handle, |driver| {
        driver.poll_snapshot.get(index as usize).map(|c| c.flags).unwrap_or(0)
    })
    .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_driver_poll_data(handle: i64, index: i64) -> RuntimeValue {
    with_driver_mut(handle, |driver| {
        let Some(completion) = driver.poll_snapshot.get(index as usize) else {
            return rt_string_new(std::ptr::null(), 0);
        };
        rt_string_new(completion.data.as_ptr(), completion.data.len() as u64)
    })
    .unwrap_or(RuntimeValue::NIL)
}

#[no_mangle]
pub extern "C" fn rt_driver_poll_data_len(handle: i64, index: i64) -> i64 {
    with_driver_mut(handle, |driver| {
        driver
            .poll_snapshot
            .get(index as usize)
            .map(|c| c.data.len() as i64)
            .unwrap_or(0)
    })
    .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_driver_cancel(_handle: i64, _op_id: i64) -> bool {
    false
}

#[no_mangle]
pub extern "C" fn rt_driver_backend_name(_handle: i64) -> RuntimeValue {
    let name = b"rust-syscall";
    rt_string_new(name.as_ptr(), name.len() as u64)
}

#[no_mangle]
pub extern "C" fn rt_driver_supports_sendfile(_handle: i64) -> bool {
    cfg!(target_os = "linux")
}

#[no_mangle]
pub extern "C" fn rt_driver_supports_zero_copy(_handle: i64) -> bool {
    cfg!(target_os = "linux")
}
