use std::io;
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

use crate::value::{rt_string_new, RuntimeValue};

const NEG_ENOSYS: i64 = -38;
const NEG_EINVAL: i64 = -22;
#[cfg(windows)]
const NEG_EIO: i64 = -5;

#[derive(Clone)]
struct Completion {
    id: i64,
    result: i64,
    flags: i64,
    data: Vec<u8>,
}

#[cfg(target_os = "linux")]
#[repr(C)]
struct CCompletion {
    id: i64,
    result: i64,
    flags: i64,
    data: *mut u8,
    data_len: i64,
}

#[cfg(target_os = "linux")]
#[repr(C)]
struct CSplDriver {
    _private: [u8; 0],
}

#[cfg(target_os = "linux")]
unsafe extern "C" {
    fn spl_driver_create_uring(queue_depth: i64) -> *mut CSplDriver;
    fn spl_driver_destroy(driver: *mut CSplDriver);
    fn spl_driver_submit_accept(driver: *mut CSplDriver, listen_fd: i64) -> i64;
    fn spl_driver_submit_connect(driver: *mut CSplDriver, fd: i64, addr: *const i8, port: i64) -> i64;
    fn spl_driver_submit_recv(driver: *mut CSplDriver, fd: i64, buf_size: i64) -> i64;
    fn spl_driver_submit_send(driver: *mut CSplDriver, fd: i64, data: *const i8, len: i64) -> i64;
    fn spl_driver_submit_sendfile(
        driver: *mut CSplDriver,
        sock_fd: i64,
        file_fd: i64,
        offset: i64,
        len: i64,
    ) -> i64;
    fn spl_driver_submit_read(driver: *mut CSplDriver, fd: i64, buf_size: i64, offset: i64) -> i64;
    fn spl_driver_submit_write(
        driver: *mut CSplDriver,
        fd: i64,
        data: *const i8,
        len: i64,
        offset: i64,
    ) -> i64;
    fn spl_driver_submit_open(driver: *mut CSplDriver, path: *const i8, flags: i64, mode: i64) -> i64;
    fn spl_driver_submit_close(driver: *mut CSplDriver, fd: i64) -> i64;
    fn spl_driver_submit_fsync(driver: *mut CSplDriver, fd: i64) -> i64;
    fn spl_driver_submit_timeout(driver: *mut CSplDriver, timeout_ms: i64) -> i64;
    fn spl_driver_flush(driver: *mut CSplDriver) -> i64;
    fn spl_driver_poll(
        driver: *mut CSplDriver,
        out: *mut CCompletion,
        max: i64,
        timeout_ms: i64,
    ) -> i64;
    fn spl_driver_cancel(driver: *mut CSplDriver, op_id: i64) -> bool;
    fn spl_driver_backend_name(driver: *mut CSplDriver) -> *const i8;
    fn spl_driver_supports_sendfile(driver: *mut CSplDriver) -> bool;
    fn spl_driver_supports_zero_copy(driver: *mut CSplDriver) -> bool;
    fn spl_completion_release(completion: *mut CCompletion);
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

enum Backend {
    Software,
    #[cfg(target_os = "linux")]
    LinuxUring(usize),
}

impl Drop for Backend {
    fn drop(&mut self) {
        #[cfg(target_os = "linux")]
        if let Backend::LinuxUring(raw) = self {
            // Every LinuxUring value is created by spl_driver_create_uring and
            // owns exactly one C driver.  Store the pointer as usize so the
            // enclosing driver remains movable through the mutex table.
            unsafe { spl_driver_destroy(*raw as *mut CSplDriver) };
        }
    }
}

struct Driver {
    backend: Backend,
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
            backend: Backend::Software,
            queue: Vec::with_capacity(capacity),
            completions: Vec::with_capacity(capacity.min(1024)),
            poll_snapshot: Vec::with_capacity(capacity.min(1024)),
        }
    }

    #[cfg(target_os = "linux")]
    fn from_linux_uring(raw: *mut CSplDriver) -> Self {
        Self {
            backend: Backend::LinuxUring(raw as usize),
            next_id: 1,
            queue: Vec::new(),
            completions: Vec::new(),
            poll_snapshot: Vec::new(),
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

    fn submit_accept(&mut self, listen_fd: i64) -> i64 {
        #[cfg(target_os = "linux")]
        if let Some(driver) = linux_uring_ptr(self) {
            return unsafe { spl_driver_submit_accept(driver, listen_fd) };
        }
        let id = self.alloc_id();
        self.submit(Operation::Accept { id, listen_fd })
    }

    fn submit_connect(&mut self, fd: i64, addr: *const i8, addr_len: i64, port: i64) -> i64 {
        #[cfg(target_os = "linux")]
        if let Some(driver) = linux_uring_ptr(self) {
            let Some(bytes) = (unsafe { bytes_from_raw(addr.cast(), addr_len) }) else { return -1; };
            let Ok(c_addr) = std::ffi::CString::new(bytes) else { return NEG_EINVAL; };
            return unsafe { spl_driver_submit_connect(driver, fd, c_addr.as_ptr().cast(), port) };
        }
        let _ = (fd, addr, addr_len, port);
        NEG_ENOSYS
    }

    fn submit_recv(&mut self, fd: i64, size: i64) -> i64 {
        #[cfg(target_os = "linux")]
        if let Some(driver) = linux_uring_ptr(self) {
            return unsafe { spl_driver_submit_recv(driver, fd, size) };
        }
        let id = self.alloc_id();
        self.submit(Operation::Recv { id, fd, size })
    }

    fn submit_send(&mut self, fd: i64, data: *const i8, len: i64) -> i64 {
        #[cfg(target_os = "linux")]
        if let Some(driver) = linux_uring_ptr(self) {
            return unsafe { spl_driver_submit_send(driver, fd, data, len) };
        }
        let Some(bytes) = (unsafe { bytes_from_raw(data.cast(), len) }) else { return -1; };
        let id = self.alloc_id();
        self.submit(Operation::Send { id, fd, data: bytes.to_vec() })
    }

    fn submit_sendfile(&mut self, sock_fd: i64, file_fd: i64, offset: i64, len: i64) -> i64 {
        #[cfg(target_os = "linux")]
        if let Some(driver) = linux_uring_ptr(self) {
            return unsafe { spl_driver_submit_sendfile(driver, sock_fd, file_fd, offset, len) };
        }
        let id = self.alloc_id();
        self.submit(Operation::Sendfile { id, sock_fd, file_fd, offset, len })
    }

    fn submit_read(&mut self, fd: i64, size: i64, offset: i64) -> i64 {
        #[cfg(target_os = "linux")]
        if let Some(driver) = linux_uring_ptr(self) {
            return unsafe { spl_driver_submit_read(driver, fd, size, offset) };
        }
        let id = self.alloc_id();
        self.submit(Operation::Read { id, fd, size, offset })
    }

    fn submit_write(&mut self, fd: i64, data: *const i8, len: i64, offset: i64) -> i64 {
        #[cfg(target_os = "linux")]
        if let Some(driver) = linux_uring_ptr(self) {
            return unsafe { spl_driver_submit_write(driver, fd, data, len, offset) };
        }
        let Some(bytes) = (unsafe { bytes_from_raw(data.cast(), len) }) else { return -1; };
        let id = self.alloc_id();
        self.submit(Operation::Write { id, fd, data: bytes.to_vec(), offset })
    }

    fn submit_open(&mut self, path: *const i8, path_len: i64, flags: i64, mode: i64) -> i64 {
        let Some(bytes) = (unsafe { bytes_from_raw(path.cast(), path_len) }) else { return -1; };
        #[cfg(target_os = "linux")]
        if let Some(driver) = linux_uring_ptr(self) {
            let Ok(c_path) = std::ffi::CString::new(bytes) else { return NEG_EINVAL; };
            return unsafe { spl_driver_submit_open(driver, c_path.as_ptr().cast(), flags, mode) };
        }
        let Ok(path) = std::str::from_utf8(bytes) else { return -1; };
        let id = self.alloc_id();
        self.submit(Operation::Open { id, path: path.to_string(), flags, mode })
    }

    fn submit_close(&mut self, fd: i64) -> i64 {
        #[cfg(target_os = "linux")]
        if let Some(driver) = linux_uring_ptr(self) {
            return unsafe { spl_driver_submit_close(driver, fd) };
        }
        let id = self.alloc_id();
        self.submit(Operation::Close { id, fd })
    }

    fn submit_fsync(&mut self, fd: i64) -> i64 {
        #[cfg(target_os = "linux")]
        if let Some(driver) = linux_uring_ptr(self) {
            return unsafe { spl_driver_submit_fsync(driver, fd) };
        }
        let id = self.alloc_id();
        self.submit(Operation::Fsync { id, fd })
    }

    fn submit_timeout(&mut self, timeout_ms: i64) -> i64 {
        #[cfg(target_os = "linux")]
        if let Some(driver) = linux_uring_ptr(self) {
            return unsafe { spl_driver_submit_timeout(driver, timeout_ms) };
        }
        let id = self.alloc_id();
        self.submit(Operation::Timeout { id, timeout_ms })
    }

    fn flush(&mut self) -> i64 {
        #[cfg(target_os = "linux")]
        if let Some(driver) = linux_uring_ptr(self) {
            return unsafe { spl_driver_flush(driver) };
        }
        let queued: Vec<_> = self.queue.drain(..).collect();
        let count = queued.len() as i64;
        self.completions.extend(queued.into_iter().map(execute_operation));
        count
    }

    #[cfg(target_os = "linux")]
    fn poll_linux_uring(&mut self, driver: *mut CSplDriver, max: i64, timeout_ms: i64) -> i64 {
        let limit = max.clamp(0, 4096) as usize;
        if limit == 0 {
            self.poll_snapshot.clear();
            return 0;
        }
        let mut raw: Vec<CCompletion> = (0..limit)
            .map(|_| CCompletion {
                id: 0,
                result: 0,
                flags: 0,
                data: std::ptr::null_mut(),
                data_len: 0,
            })
            .collect();
        let count = unsafe { spl_driver_poll(driver, raw.as_mut_ptr(), limit as i64, timeout_ms) };
        if count <= 0 {
            self.poll_snapshot.clear();
            return count;
        }
        let count = (count as usize).min(limit);
        self.poll_snapshot.clear();
        self.poll_snapshot.reserve(count);
        for completion in raw.iter_mut().take(count) {
            let data = if completion.data.is_null() || completion.data_len <= 0 {
                Vec::new()
            } else {
                unsafe {
                    std::slice::from_raw_parts(completion.data, completion.data_len as usize).to_vec()
                }
            };
            self.poll_snapshot.push(Completion {
                id: completion.id,
                result: completion.result,
                flags: completion.flags,
                data,
            });
            unsafe { spl_completion_release(completion) };
        }
        count as i64
    }

    fn poll(&mut self, max: i64, timeout_ms: i64) -> i64 {
        #[cfg(target_os = "linux")]
        if let Some(driver) = linux_uring_ptr(self) {
            return self.poll_linux_uring(driver, max, timeout_ms);
        }
        let limit = max.clamp(0, 4096) as usize;
        let deadline = if timeout_ms > 0 {
            Some(Instant::now() + Duration::from_millis(timeout_ms as u64))
        } else {
            None
        };
        while self.completions.is_empty() && timeout_ms != 0 {
            if let Some(deadline) = deadline {
                if Instant::now() >= deadline { break; }
            }
            std::thread::sleep(Duration::from_millis(1));
        }
        let count = limit.min(self.completions.len());
        self.poll_snapshot = self.completions.drain(0..count).collect();
        count as i64
    }

    fn cancel(&mut self, op_id: i64) -> bool {
        #[cfg(target_os = "linux")]
        if let Some(driver) = linux_uring_ptr(self) {
            return unsafe { spl_driver_cancel(driver, op_id) };
        }
        false
    }

    fn backend_name(&self) -> &'static str {
        #[cfg(target_os = "linux")]
        if let Some(driver) = linux_uring_ptr(self) {
            let name = unsafe { std::ffi::CStr::from_ptr(spl_driver_backend_name(driver).cast()) };
            return if name.to_bytes() == b"io_uring" { "io_uring" } else { "native" };
        }
        "rust-syscall"
    }

    fn supports_sendfile(&self) -> bool {
        #[cfg(target_os = "linux")]
        if let Some(driver) = linux_uring_ptr(self) {
            return unsafe { spl_driver_supports_sendfile(driver) };
        }
        cfg!(target_os = "linux")
    }

    fn supports_zero_copy(&self) -> bool {
        #[cfg(target_os = "linux")]
        if let Some(driver) = linux_uring_ptr(self) {
            return unsafe { spl_driver_supports_zero_copy(driver) };
        }
        cfg!(target_os = "linux")
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

#[cfg(target_os = "linux")]
fn linux_uring_ptr(driver: &Driver) -> Option<*mut CSplDriver> {
    match &driver.backend {
        Backend::LinuxUring(raw) => Some(*raw as *mut CSplDriver),
        Backend::Software => None,
    }
}

fn with_driver_mut<R>(handle: i64, f: impl FnOnce(&mut Driver) -> R) -> Option<R> {
    let mut guard = drivers().lock().ok()?;
    let driver = guard.get_mut(handle as usize)?.as_mut()?;
    Some(f(driver))
}

fn create_driver(queue_depth: i64) -> Result<Driver, i64> {
    let requested = std::env::var("SIMPLE_SOSIX_PROVIDER")
        .unwrap_or_else(|_| "auto".to_string())
        .trim()
        .to_ascii_lowercase();
    match requested.as_str() {
        "" | "auto" => {
            #[cfg(target_os = "linux")]
            {
                let raw = unsafe { spl_driver_create_uring(queue_depth) };
                if !raw.is_null() {
                    return Ok(Driver::from_linux_uring(raw));
                }
            }
            Ok(Driver::new(queue_depth))
        }
        "io_uring" | "io-uring" | "uring" => {
            #[cfg(target_os = "linux")]
            {
                let raw = unsafe { spl_driver_create_uring(queue_depth) };
                if raw.is_null() {
                    // An explicit provider is a capability request.  Do not
                    // silently downgrade it to the reference implementation.
                    return Err(NEG_ENOSYS);
                }
                return Ok(Driver::from_linux_uring(raw));
            }
            #[cfg(not(target_os = "linux"))]
            {
                Err(NEG_ENOSYS)
            }
        }
        "reference" | "rust-syscall" | "fallback" | "epoll" | "kqueue" | "iocp" => {
            Ok(Driver::new(queue_depth))
        }
        _ => Err(NEG_EINVAL),
    }
}

#[cfg(unix)]
fn os_error_code() -> i64 {
    -(io::Error::last_os_error().raw_os_error().unwrap_or(libc::EIO) as i64)
}

#[cfg(windows)]
fn os_error_code() -> i64 {
    -(io::Error::last_os_error().raw_os_error().unwrap_or(NEG_EIO as i32) as i64)
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

#[cfg(unix)]
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
            let fd = unsafe {
                libc::open(
                    c_path.as_ptr(),
                    flags as libc::c_int,
                    mode as libc::mode_t as libc::c_uint,
                )
            };
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

#[cfg(windows)]
fn execute_operation(operation: Operation) -> Completion {
    match operation {
        Operation::Timeout { id, timeout_ms } => {
            if timeout_ms > 0 {
                std::thread::sleep(Duration::from_millis(timeout_ms as u64));
            }
            completion(id, 0)
        }
        Operation::Accept { id, .. }
        | Operation::Recv { id, .. }
        | Operation::Send { id, .. }
        | Operation::Sendfile { id, .. }
        | Operation::Read { id, .. }
        | Operation::Write { id, .. }
        | Operation::Open { id, .. }
        | Operation::Close { id, .. }
        | Operation::Fsync { id, .. } => completion(id, NEG_ENOSYS),
    }
}

#[no_mangle]
pub extern "C" fn rt_driver_create(queue_depth: i64) -> i64 {
    let mut guard = match drivers().lock() {
        Ok(guard) => guard,
        Err(_) => return NEG_EINVAL,
    };
    let driver = match create_driver(queue_depth) {
        Ok(driver) => driver,
        Err(status) => return status,
    };
    if let Some((index, slot)) = guard.iter_mut().enumerate().find(|(_, slot)| slot.is_none()) {
        *slot = Some(driver);
        return index as i64;
    }
    guard.push(Some(driver));
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
    with_driver_mut(handle, |driver| driver.submit_accept(listen_fd))
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
    with_driver_mut(_handle, |driver| driver.submit_connect(_fd, _addr.cast(), _addr_len, _port))
        .unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn rt_driver_submit_recv(handle: i64, fd: i64, buf_size: i64) -> i64 {
    with_driver_mut(handle, |driver| driver.submit_recv(fd, buf_size))
    .unwrap_or(-1)
}

#[no_mangle]
pub unsafe extern "C" fn rt_driver_submit_send(handle: i64, fd: i64, data: *const u8, len: i64) -> i64 {
    with_driver_mut(handle, |driver| driver.submit_send(fd, data.cast(), len))
    .unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn rt_driver_submit_sendfile(handle: i64, sock_fd: i64, file_fd: i64, offset: i64, len: i64) -> i64 {
    with_driver_mut(handle, |driver| driver.submit_sendfile(sock_fd, file_fd, offset, len))
    .unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn rt_driver_submit_read(handle: i64, fd: i64, buf_size: i64, offset: i64) -> i64 {
    with_driver_mut(handle, |driver| driver.submit_read(fd, buf_size, offset))
    .unwrap_or(-1)
}

#[no_mangle]
pub unsafe extern "C" fn rt_driver_submit_write(handle: i64, fd: i64, data: *const u8, len: i64, offset: i64) -> i64 {
    with_driver_mut(handle, |driver| driver.submit_write(fd, data.cast(), len, offset))
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
    with_driver_mut(handle, |driver| driver.submit_open(path.cast(), path_len, flags, mode))
    .unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn rt_driver_submit_close(handle: i64, fd: i64) -> i64 {
    with_driver_mut(handle, |driver| driver.submit_close(fd))
    .unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn rt_driver_submit_fsync(handle: i64, fd: i64) -> i64 {
    with_driver_mut(handle, |driver| driver.submit_fsync(fd))
    .unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn rt_driver_submit_timeout(handle: i64, timeout_ms: i64) -> i64 {
    with_driver_mut(handle, |driver| driver.submit_timeout(timeout_ms))
    .unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn rt_driver_flush(handle: i64) -> i64 {
    with_driver_mut(handle, |driver| driver.flush())
    .unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn rt_driver_poll(handle: i64, max: i64, timeout_ms: i64) -> i64 {
    with_driver_mut(handle, |driver| driver.poll(max, timeout_ms))
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

/// Raw pointer view used only by the interpreter bridge.  Native Simple text
/// calls use rt_driver_poll_data, which returns a managed RuntimeValue; the
/// interpreter must not reinterpret that tagged value as a C string pointer.
#[no_mangle]
pub extern "C" fn rt_driver_poll_data_ptr(handle: i64, index: i64) -> *const u8 {
    with_driver_mut(handle, |driver| {
        driver
            .poll_snapshot
            .get(index as usize)
            .map(|completion| completion.data.as_ptr())
            .unwrap_or(std::ptr::null())
    })
    .unwrap_or(std::ptr::null())
}

#[no_mangle]
pub extern "C" fn rt_driver_cancel(_handle: i64, _op_id: i64) -> bool {
    with_driver_mut(_handle, |driver| driver.cancel(_op_id)).unwrap_or(false)
}

#[no_mangle]
pub extern "C" fn rt_driver_backend_name(handle: i64) -> RuntimeValue {
    let name = with_driver_mut(handle, |driver| driver.backend_name())
        .unwrap_or("none");
    rt_string_new(name.as_ptr(), name.len() as u64)
}

#[no_mangle]
pub extern "C" fn rt_driver_backend_name_ptr(handle: i64) -> *const u8 {
    static IO_URING: &[u8] = b"io_uring\0";
    static RUST_SYSCALL: &[u8] = b"rust-syscall\0";
    static NONE: &[u8] = b"none\0";
    match with_driver_mut(handle, |driver| driver.backend_name()).unwrap_or("none") {
        "io_uring" => IO_URING.as_ptr(),
        "rust-syscall" => RUST_SYSCALL.as_ptr(),
        _ => NONE.as_ptr(),
    }
}

#[no_mangle]
pub extern "C" fn rt_driver_supports_sendfile(handle: i64) -> bool {
    with_driver_mut(handle, |driver| driver.supports_sendfile()).unwrap_or(false)
}

#[no_mangle]
pub extern "C" fn rt_driver_supports_zero_copy(handle: i64) -> bool {
    with_driver_mut(handle, |driver| driver.supports_zero_copy()).unwrap_or(false)
}

#[cfg(all(test, target_os = "linux"))]
mod tests {
    use super::*;
    use std::ffi::CString;
    use std::fs;
    use std::os::raw::c_char;

    #[test]
    fn io_uring_provider_completes_positioned_io_and_cancellation_once() {
        let handle = rt_driver_create(32);
        assert!(handle >= 0, "io_uring must be available for this Linux acceptance");
        let backend = rt_driver_backend_name_ptr(handle);
        assert_eq!(unsafe { std::ffi::CStr::from_ptr(backend.cast::<c_char>()) }.to_bytes(), b"io_uring");

        let path = std::env::temp_dir().join(format!("simple-io-uring-{}", std::process::id()));
        let _ = fs::remove_file(&path);
        let path_c = CString::new(path.to_string_lossy().as_bytes()).unwrap();
        let open = unsafe { rt_driver_submit_open(handle, path_c.as_ptr().cast(), path_c.as_bytes().len() as i64, 66, 0o644) };
        assert!(open > 0);
        assert_eq!(rt_driver_flush(handle), 1);
        assert_eq!(rt_driver_poll(handle, 1, 1000), 1);
        let fd = rt_driver_poll_result(handle, 0);
        assert!(fd >= 0);

        let bytes = b"uring";
        let write = unsafe { rt_driver_submit_write(handle, fd, bytes.as_ptr().cast(), bytes.len() as i64, 3) };
        assert!(write > 0);
        assert_eq!(rt_driver_flush(handle), 1);
        assert_eq!(rt_driver_poll(handle, 1, 1000), 1);
        assert_eq!(rt_driver_poll_result(handle, 0), bytes.len() as i64);

        let read = rt_driver_submit_read(handle, fd, 16, 3);
        assert!(read > 0);
        assert_eq!(rt_driver_flush(handle), 1);
        assert_eq!(rt_driver_poll(handle, 1, 1000), 1);
        assert_eq!(rt_driver_poll_result(handle, 0), bytes.len() as i64);
        let data = rt_driver_poll_data_ptr(handle, 0);
        let data_len = rt_driver_poll_data_len(handle, 0) as usize;
        assert_eq!(unsafe { std::slice::from_raw_parts(data, data_len) }, bytes);

        let timeout = rt_driver_submit_timeout(handle, 10_000);
        assert!(timeout > 0);
        assert!(rt_driver_cancel(handle, timeout));
        assert_eq!(rt_driver_flush(handle), 2);
        assert_eq!(rt_driver_poll(handle, 2, 1000), 1);
        assert_eq!(rt_driver_poll_id(handle, 0), timeout);
        assert_eq!(rt_driver_poll_result(handle, 0), -libc::ECANCELED as i64);

        let close = rt_driver_submit_close(handle, fd);
        assert!(close > 0);
        assert_eq!(rt_driver_flush(handle), 1);
        assert_eq!(rt_driver_poll(handle, 1, 1000), 1);
        assert_eq!(rt_driver_poll_result(handle, 0), 0);
        rt_driver_destroy(handle);
        let _ = fs::remove_file(path);
    }
}
