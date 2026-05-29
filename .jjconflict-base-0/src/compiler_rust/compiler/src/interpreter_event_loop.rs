//! Event loop externs for the Simple interpreter
//!
//! Implements `rt_event_loop_*` extern functions using the platform-native
//! I/O notification mechanism:
//!
//! - **epoll** on Linux — level/edge-triggered, O(1) readiness notification
//! - **kqueue** on macOS/FreeBSD — edge-triggered by default, filter-based
//! - **IOCP** on Windows — completion-based (proactor), stub with WSAPoll fallback
//! - **event ports** on Solaris/illumos — port_create/port_associate/port_get, one-shot
//! - **poll fallback** on other platforms — returns error values
//!
//! Handle pool starts at 3000 to avoid collisions with SOCKET_HANDLES (1000+).

use crate::error::CompileError;
use crate::value::Value;
use std::sync::atomic::{AtomicI64, Ordering};

static NEXT_EVENT_LOOP_HANDLE: AtomicI64 = AtomicI64::new(3000);

// ---------------------------------------------------------------------------
// Linux — epoll
// ---------------------------------------------------------------------------
#[cfg(target_os = "linux")]
mod platform {
    use super::*;
    use std::cell::RefCell;
    use std::collections::HashMap;

    /// Per event-loop state: raw epoll fd + fd-to-token side-table.
    /// The side-table preserves full i64 token width (epoll_event.u64
    /// carries the fd so the kernel tells us which descriptor fired).
    struct EpollState {
        epfd: i32,
        tokens: HashMap<i32, i64>, // monitored fd -> caller token
    }

    thread_local! {
        static EPOLL_LOOPS: RefCell<HashMap<i64, EpollState>> = RefCell::new(HashMap::new());
    }

    pub fn create() -> i64 {
        let epfd = unsafe { libc::epoll_create1(0) };
        if epfd < 0 {
            return -1;
        }
        let handle = NEXT_EVENT_LOOP_HANDLE.fetch_add(1, Ordering::SeqCst);
        EPOLL_LOOPS.with(|loops| {
            loops.borrow_mut().insert(
                handle,
                EpollState {
                    epfd,
                    tokens: HashMap::new(),
                },
            );
        });
        handle
    }

    pub fn register(loop_fd: i64, fd: i64, interest: i64, token: i64, edge: bool) -> bool {
        EPOLL_LOOPS.with(|loops| {
            let mut loops = loops.borrow_mut();
            let Some(state) = loops.get_mut(&loop_fd) else {
                return false;
            };

            let mut events: u32 = 0;
            match interest {
                0 => events |= libc::EPOLLIN as u32,
                1 => events |= libc::EPOLLOUT as u32,
                2 => events |= (libc::EPOLLIN | libc::EPOLLOUT) as u32,
                _ => events |= libc::EPOLLIN as u32,
            }
            if edge {
                events |= libc::EPOLLET as u32;
            }

            // Store fd in data.u64 so poll() knows which descriptor fired
            let mut ev = libc::epoll_event { events, u64: fd as u64 };

            let ret = unsafe { libc::epoll_ctl(state.epfd, libc::EPOLL_CTL_ADD, fd as i32, &mut ev) };
            if ret < 0 {
                // Try MOD in case it was already registered
                let ret2 = unsafe { libc::epoll_ctl(state.epfd, libc::EPOLL_CTL_MOD, fd as i32, &mut ev) };
                if ret2 != 0 {
                    return false;
                }
            }
            // Store full i64 token in side-table
            state.tokens.insert(fd as i32, token);
            true
        })
    }

    pub fn deregister(loop_fd: i64, fd: i64) -> bool {
        EPOLL_LOOPS.with(|loops| {
            let mut loops = loops.borrow_mut();
            let Some(state) = loops.get_mut(&loop_fd) else {
                return false;
            };
            state.tokens.remove(&(fd as i32));
            let ret = unsafe { libc::epoll_ctl(state.epfd, libc::EPOLL_CTL_DEL, fd as i32, std::ptr::null_mut()) };
            ret == 0
        })
    }

    pub fn poll(loop_fd: i64, max_events: i64, timeout_ms: i64) -> Vec<Value> {
        EPOLL_LOOPS.with(|loops| {
            let loops = loops.borrow();
            let Some(state) = loops.get(&loop_fd) else {
                return vec![];
            };

            let max = max_events.clamp(1, 1024) as usize;
            let mut events: Vec<libc::epoll_event> = vec![libc::epoll_event { events: 0, u64: 0 }; max];

            let n = unsafe { libc::epoll_wait(state.epfd, events.as_mut_ptr(), max as i32, timeout_ms as i32) };
            if n < 0 {
                return vec![];
            }

            let mut result = Vec::with_capacity(n as usize * 3);
            for i in 0..n as usize {
                let ev = &events[i];
                let stored_fd = ev.u64 as i64;
                // Look up full i64 token from side-table
                let stored_token = state.tokens.get(&(stored_fd as i32)).copied().unwrap_or(0);

                // Map epoll event flags back to interest encoding
                let readable = (ev.events & libc::EPOLLIN as u32) != 0;
                let writable = (ev.events & libc::EPOLLOUT as u32) != 0;
                let ready: i64 = match (readable, writable) {
                    (true, true) => 2,  // ReadWrite
                    (false, true) => 1, // Write
                    _ => 0,             // Read (or error/hup treated as read-ready)
                };

                result.push(Value::Int(stored_fd));
                result.push(Value::Int(ready));
                result.push(Value::Int(stored_token));
            }
            result
        })
    }

    pub fn close(loop_fd: i64) -> bool {
        EPOLL_LOOPS.with(|loops| {
            let mut loops = loops.borrow_mut();
            if let Some(state) = loops.remove(&loop_fd) {
                unsafe { libc::close(state.epfd) };
                true
            } else {
                false
            }
        })
    }

    pub fn clear_state() {
        EPOLL_LOOPS.with(|loops| {
            let mut map = loops.borrow_mut();
            for (_, state) in map.drain() {
                unsafe { libc::close(state.epfd) };
            }
        });
    }

    pub fn backend_name() -> &'static str {
        "epoll"
    }
}

// ---------------------------------------------------------------------------
// macOS / FreeBSD — kqueue
// ---------------------------------------------------------------------------
#[cfg(any(target_os = "macos", target_os = "freebsd"))]
mod platform {
    use super::*;
    use std::cell::RefCell;
    use std::collections::HashMap;

    thread_local! {
        /// Maps handle id -> raw kqueue fd
        static KQUEUE_FDS: RefCell<HashMap<i64, i32>> = RefCell::new(HashMap::new());
    }

    pub fn create() -> i64 {
        let kqfd = unsafe { libc::kqueue() };
        if kqfd < 0 {
            return -1;
        }
        let handle = NEXT_EVENT_LOOP_HANDLE.fetch_add(1, Ordering::SeqCst);
        KQUEUE_FDS.with(|fds| fds.borrow_mut().insert(handle, kqfd));
        handle
    }

    pub fn register(loop_fd: i64, fd: i64, interest: i64, token: i64, edge: bool) -> bool {
        KQUEUE_FDS.with(|fds| {
            let fds = fds.borrow();
            let Some(&kqfd) = fds.get(&loop_fd) else {
                return false;
            };

            let flags: u16 = if edge {
                libc::EV_ADD as u16 | libc::EV_CLEAR as u16
            } else {
                libc::EV_ADD as u16
            };

            let mut changes: Vec<libc::kevent> = Vec::with_capacity(2);

            // interest: 0=Read, 1=Write, 2=ReadWrite
            if interest == 0 || interest == 2 {
                changes.push(libc::kevent {
                    ident: fd as libc::uintptr_t,
                    filter: libc::EVFILT_READ,
                    flags,
                    fflags: 0,
                    data: 0,
                    udata: token as *mut libc::c_void,
                });
            }
            if interest == 1 || interest == 2 {
                changes.push(libc::kevent {
                    ident: fd as libc::uintptr_t,
                    filter: libc::EVFILT_WRITE,
                    flags,
                    fflags: 0,
                    data: 0,
                    udata: token as *mut libc::c_void,
                });
            }

            if changes.is_empty() {
                return false;
            }

            let ret = unsafe {
                libc::kevent(
                    kqfd,
                    changes.as_ptr(),
                    changes.len() as i32,
                    std::ptr::null_mut(),
                    0,
                    std::ptr::null(),
                )
            };
            ret >= 0
        })
    }

    pub fn deregister(loop_fd: i64, fd: i64) -> bool {
        KQUEUE_FDS.with(|fds| {
            let fds = fds.borrow();
            let Some(&kqfd) = fds.get(&loop_fd) else {
                return false;
            };

            // Remove both filters; ignore ENOENT if one wasn't registered
            let changes = [
                libc::kevent {
                    ident: fd as libc::uintptr_t,
                    filter: libc::EVFILT_READ,
                    flags: libc::EV_DELETE as u16,
                    fflags: 0,
                    data: 0,
                    udata: std::ptr::null_mut(),
                },
                libc::kevent {
                    ident: fd as libc::uintptr_t,
                    filter: libc::EVFILT_WRITE,
                    flags: libc::EV_DELETE as u16,
                    fflags: 0,
                    data: 0,
                    udata: std::ptr::null_mut(),
                },
            ];

            // Best-effort: at least one delete should succeed
            let ret = unsafe { libc::kevent(kqfd, changes.as_ptr(), 2, std::ptr::null_mut(), 0, std::ptr::null()) };
            // ret < 0 with ENOENT is acceptable (filter wasn't registered)
            let _ = ret;
            true
        })
    }

    pub fn poll(loop_fd: i64, max_events: i64, timeout_ms: i64) -> Vec<Value> {
        KQUEUE_FDS.with(|fds| {
            let fds = fds.borrow();
            let Some(&kqfd) = fds.get(&loop_fd) else {
                return vec![];
            };

            let max = max_events.clamp(1, 1024) as usize;
            let mut events: Vec<libc::kevent> = vec![
                libc::kevent {
                    ident: 0,
                    filter: 0,
                    flags: 0,
                    fflags: 0,
                    data: 0,
                    udata: std::ptr::null_mut(),
                };
                max
            ];

            let timeout = if timeout_ms < 0 {
                std::ptr::null()
            } else {
                &libc::timespec {
                    tv_sec: timeout_ms / 1000,
                    tv_nsec: (timeout_ms % 1000) * 1_000_000,
                } as *const libc::timespec
            };

            let n = unsafe { libc::kevent(kqfd, std::ptr::null(), 0, events.as_mut_ptr(), max as i32, timeout) };
            if n < 0 {
                return vec![];
            }

            // Coalesce multiple filter events for the same (fd, token) pair
            // into a single ReadWrite entry
            use std::collections::HashMap;
            let mut merged: HashMap<(i64, i64), i64> = HashMap::new();
            // Preserve insertion order
            let mut order: Vec<(i64, i64)> = Vec::new();

            for i in 0..n as usize {
                let ev = &events[i];
                let ev_fd = ev.ident as i64;
                let ev_token = ev.udata as i64;
                let ready: i64 = if ev.filter == libc::EVFILT_READ {
                    0 // Read
                } else if ev.filter == libc::EVFILT_WRITE {
                    1 // Write
                } else {
                    0 // Default to Read
                };

                let key = (ev_fd, ev_token);
                let entry = merged.entry(key).or_insert_with(|| {
                    order.push(key);
                    -1 // sentinel
                });
                if *entry == -1 {
                    *entry = ready;
                } else if *entry != ready {
                    *entry = 2; // ReadWrite
                }
            }

            let mut result = Vec::with_capacity(order.len() * 3);
            for (fd, token) in order {
                let ready = merged[&(fd, token)];
                result.push(Value::Int(fd));
                result.push(Value::Int(ready));
                result.push(Value::Int(token));
            }
            result
        })
    }

    pub fn close(loop_fd: i64) -> bool {
        KQUEUE_FDS.with(|fds| {
            let mut fds = fds.borrow_mut();
            if let Some(kqfd) = fds.remove(&loop_fd) {
                unsafe { libc::close(kqfd) };
                true
            } else {
                false
            }
        })
    }

    pub fn clear_state() {
        KQUEUE_FDS.with(|fds| {
            let mut map = fds.borrow_mut();
            for (_, kqfd) in map.drain() {
                unsafe { libc::close(kqfd) };
            }
        });
    }

    pub fn backend_name() -> &'static str {
        "kqueue"
    }
}

// ---------------------------------------------------------------------------
// Windows — IOCP stub
// ---------------------------------------------------------------------------
// IOCP is completion-based (proactor pattern), not readiness-based like
// epoll/kqueue. A full implementation requires an adaptation layer to
// provide readiness semantics to the Simple event loop API. For now this
// is a stub that allocates handles but returns error values from I/O
// operations, with TODO for full proactor-to-reactor adaptation using
// WSAPoll as a transitional fallback.
#[cfg(target_os = "windows")]
mod platform {
    use super::*;
    use std::cell::RefCell;
    use std::collections::HashMap;

    thread_local! {
        /// Maps handle id -> unit (no native fd yet; IOCP handle TBD)
        static IOCP_LOOPS: RefCell<HashMap<i64, ()>> = RefCell::new(HashMap::new());
    }

    pub fn create() -> i64 {
        // TODO: CreateIoCompletionPort(INVALID_HANDLE_VALUE, NULL, 0, 0)
        // For now, allocate a handle so callers can distinguish "created
        // but unsupported ops" from "couldn't create at all".
        let handle = NEXT_EVENT_LOOP_HANDLE.fetch_add(1, Ordering::SeqCst);
        IOCP_LOOPS.with(|loops| {
            loops.borrow_mut().insert(handle, ());
        });
        eprintln!("[event_loop] IOCP backend: stub — I/O operations not yet implemented");
        handle
    }

    pub fn register(_loop_fd: i64, _fd: i64, _interest: i64, _token: i64, _edge: bool) -> bool {
        // TODO: WSAPoll registration or CreateIoCompletionPort association
        eprintln!("[event_loop] IOCP register: not yet implemented");
        false
    }

    pub fn deregister(_loop_fd: i64, _fd: i64) -> bool {
        // TODO: CancelIoEx or disassociate from completion port
        eprintln!("[event_loop] IOCP deregister: not yet implemented");
        false
    }

    pub fn poll(_loop_fd: i64, _max_events: i64, _timeout_ms: i64) -> Vec<Value> {
        // TODO: GetQueuedCompletionStatusEx or WSAPoll fallback
        eprintln!("[event_loop] IOCP poll: not yet implemented");
        vec![]
    }

    pub fn close(loop_fd: i64) -> bool {
        IOCP_LOOPS.with(|loops| {
            let mut loops = loops.borrow_mut();
            if loops.remove(&loop_fd).is_some() {
                // TODO: CloseHandle on the real IOCP handle
                true
            } else {
                false
            }
        })
    }

    pub fn clear_state() {
        IOCP_LOOPS.with(|loops| {
            loops.borrow_mut().clear();
        });
    }

    pub fn backend_name() -> &'static str {
        "iocp"
    }
}

// ---------------------------------------------------------------------------
// Solaris / illumos — event ports stub
// ---------------------------------------------------------------------------
// Event ports use port_create(), port_associate(), port_get()/port_getn()
// for I/O notification. One-shot semantics — must re-associate after each
// event. For now this is a stub that allocates handles but returns error
// values from I/O operations.
#[cfg(any(target_os = "solaris", target_os = "illumos"))]
mod platform {
    use super::*;
    use std::cell::RefCell;
    use std::collections::HashMap;

    thread_local! {
        /// Maps handle id -> unit (port fd TBD)
        static PORT_LOOPS: RefCell<HashMap<i64, ()>> = RefCell::new(HashMap::new());
    }

    pub fn create() -> i64 {
        // TODO: libc::port_create()
        // Allocate a handle for API consistency.
        let handle = NEXT_EVENT_LOOP_HANDLE.fetch_add(1, Ordering::SeqCst);
        PORT_LOOPS.with(|loops| {
            loops.borrow_mut().insert(handle, ());
        });
        eprintln!("[event_loop] event_port backend: stub — I/O operations not yet implemented");
        handle
    }

    pub fn register(_loop_fd: i64, _fd: i64, _interest: i64, _token: i64, _edge: bool) -> bool {
        // TODO: port_associate(port, PORT_SOURCE_FD, fd, events, user)
        eprintln!("[event_loop] event_port register: not yet implemented");
        false
    }

    pub fn deregister(_loop_fd: i64, _fd: i64) -> bool {
        // TODO: port_dissociate(port, PORT_SOURCE_FD, fd)
        eprintln!("[event_loop] event_port deregister: not yet implemented");
        false
    }

    pub fn poll(_loop_fd: i64, _max_events: i64, _timeout_ms: i64) -> Vec<Value> {
        // TODO: port_getn(port, list, max, &nget, timeout)
        // Must re-associate fds after receiving events (one-shot semantics)
        eprintln!("[event_loop] event_port poll: not yet implemented");
        vec![]
    }

    pub fn close(loop_fd: i64) -> bool {
        PORT_LOOPS.with(|loops| {
            let mut loops = loops.borrow_mut();
            if loops.remove(&loop_fd).is_some() {
                // TODO: libc::close(port_fd)
                true
            } else {
                false
            }
        })
    }

    pub fn clear_state() {
        PORT_LOOPS.with(|loops| {
            loops.borrow_mut().clear();
        });
    }

    pub fn backend_name() -> &'static str {
        "event_port"
    }
}

// ---------------------------------------------------------------------------
// Unsupported platforms — stub returning errors
// ---------------------------------------------------------------------------
#[cfg(not(any(
    target_os = "linux",
    target_os = "macos",
    target_os = "freebsd",
    target_os = "windows",
    target_os = "solaris",
    target_os = "illumos",
)))]
mod platform {
    use super::*;

    pub fn create() -> i64 {
        -1
    }
    pub fn register(_loop_fd: i64, _fd: i64, _interest: i64, _token: i64, _edge: bool) -> bool {
        false
    }
    pub fn deregister(_loop_fd: i64, _fd: i64) -> bool {
        false
    }
    pub fn poll(_loop_fd: i64, _max_events: i64, _timeout_ms: i64) -> Vec<Value> {
        vec![]
    }
    pub fn close(_loop_fd: i64) -> bool {
        false
    }
    pub fn clear_state() {}
    pub fn backend_name() -> &'static str {
        "poll"
    }
}

// ---------------------------------------------------------------------------
// Public interpreter extern functions
// ---------------------------------------------------------------------------

pub fn rt_event_loop_create_interp(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(platform::create()))
}

pub fn rt_event_loop_register_interp(args: &[Value]) -> Result<Value, CompileError> {
    let loop_fd = args.get(0).and_then(|v| v.as_int().ok()).unwrap_or(-1);
    let fd = args.get(1).and_then(|v| v.as_int().ok()).unwrap_or(-1);
    let interest = args.get(2).and_then(|v| v.as_int().ok()).unwrap_or(0);
    let token = args.get(3).and_then(|v| v.as_int().ok()).unwrap_or(0);
    let edge = args.get(4).map(|v| v.truthy()).unwrap_or(false);
    Ok(Value::Bool(platform::register(loop_fd, fd, interest, token, edge)))
}

pub fn rt_event_loop_deregister_interp(args: &[Value]) -> Result<Value, CompileError> {
    let loop_fd = args.get(0).and_then(|v| v.as_int().ok()).unwrap_or(-1);
    let fd = args.get(1).and_then(|v| v.as_int().ok()).unwrap_or(-1);
    Ok(Value::Bool(platform::deregister(loop_fd, fd)))
}

pub fn rt_event_loop_poll_interp(args: &[Value]) -> Result<Value, CompileError> {
    let loop_fd = args.get(0).and_then(|v| v.as_int().ok()).unwrap_or(-1);
    let max_events = args.get(1).and_then(|v| v.as_int().ok()).unwrap_or(64);
    let timeout_ms = args.get(2).and_then(|v| v.as_int().ok()).unwrap_or(-1);
    Ok(Value::array(platform::poll(loop_fd, max_events, timeout_ms)))
}

pub fn rt_event_loop_close_interp(args: &[Value]) -> Result<Value, CompileError> {
    let loop_fd = args.get(0).and_then(|v| v.as_int().ok()).unwrap_or(-1);
    Ok(Value::Bool(platform::close(loop_fd)))
}

/// Clear all event loop handles (call between test runs).
pub fn clear_event_loop_state() {
    platform::clear_state();
}

/// Return which event loop backend is active on this platform.
///
/// Returns one of: `"epoll"`, `"kqueue"`, `"iocp"`, `"event_port"`, `"poll"`.
pub fn event_loop_backend_name() -> &'static str {
    platform::backend_name()
}

// ---------------------------------------------------------------------------
// Per-backend extern stubs for cross-platform dispatch from Simple
// ---------------------------------------------------------------------------
// These provide named entry points for each backend so the Simple-side
// PlatformEvent class can dispatch by backend enum. On the active platform,
// they delegate to platform::*; on all others they return stub values.

// ---- kqueue ----

pub fn rt_kqueue_create_interp(_args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(any(target_os = "macos", target_os = "freebsd"))]
    { return Ok(Value::Int(platform::create())); }
    #[cfg(not(any(target_os = "macos", target_os = "freebsd")))]
    { Ok(Value::Int(-1)) }
}

pub fn rt_kqueue_register_interp(args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(any(target_os = "macos", target_os = "freebsd"))]
    {
        let loop_fd = args.get(0).and_then(|v| v.as_int().ok()).unwrap_or(-1);
        let fd = args.get(1).and_then(|v| v.as_int().ok()).unwrap_or(-1);
        let interest = args.get(2).and_then(|v| v.as_int().ok()).unwrap_or(0);
        let token = args.get(3).and_then(|v| v.as_int().ok()).unwrap_or(0);
        let edge = args.get(4).map(|v| v.truthy()).unwrap_or(false);
        return Ok(Value::Bool(platform::register(loop_fd, fd, interest, token, edge)));
    }
    #[cfg(not(any(target_os = "macos", target_os = "freebsd")))]
    {
        let _ = args;
        Ok(Value::Bool(false))
    }
}

pub fn rt_kqueue_deregister_interp(args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(any(target_os = "macos", target_os = "freebsd"))]
    {
        let loop_fd = args.get(0).and_then(|v| v.as_int().ok()).unwrap_or(-1);
        let fd = args.get(1).and_then(|v| v.as_int().ok()).unwrap_or(-1);
        return Ok(Value::Bool(platform::deregister(loop_fd, fd)));
    }
    #[cfg(not(any(target_os = "macos", target_os = "freebsd")))]
    {
        let _ = args;
        Ok(Value::Bool(false))
    }
}

pub fn rt_kqueue_poll_interp(args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(any(target_os = "macos", target_os = "freebsd"))]
    {
        let loop_fd = args.get(0).and_then(|v| v.as_int().ok()).unwrap_or(-1);
        let max_events = args.get(1).and_then(|v| v.as_int().ok()).unwrap_or(64);
        let timeout_ms = args.get(2).and_then(|v| v.as_int().ok()).unwrap_or(-1);
        return Ok(Value::array(platform::poll(loop_fd, max_events, timeout_ms)));
    }
    #[cfg(not(any(target_os = "macos", target_os = "freebsd")))]
    {
        let _ = args;
        Ok(Value::array(vec![]))
    }
}

pub fn rt_kqueue_close_interp(args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(any(target_os = "macos", target_os = "freebsd"))]
    {
        let loop_fd = args.get(0).and_then(|v| v.as_int().ok()).unwrap_or(-1);
        return Ok(Value::Bool(platform::close(loop_fd)));
    }
    #[cfg(not(any(target_os = "macos", target_os = "freebsd")))]
    {
        let _ = args;
        Ok(Value::Bool(false))
    }
}

// ---- IOCP ----

pub fn rt_iocp_create_interp(_args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(target_os = "windows")]
    { return Ok(Value::Int(platform::create())); }
    #[cfg(not(target_os = "windows"))]
    { Ok(Value::Int(-1)) }
}

pub fn rt_iocp_register_interp(args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(target_os = "windows")]
    {
        let loop_fd = args.get(0).and_then(|v| v.as_int().ok()).unwrap_or(-1);
        let fd = args.get(1).and_then(|v| v.as_int().ok()).unwrap_or(-1);
        let interest = args.get(2).and_then(|v| v.as_int().ok()).unwrap_or(0);
        let token = args.get(3).and_then(|v| v.as_int().ok()).unwrap_or(0);
        let edge = args.get(4).map(|v| v.truthy()).unwrap_or(false);
        return Ok(Value::Bool(platform::register(loop_fd, fd, interest, token, edge)));
    }
    #[cfg(not(target_os = "windows"))]
    {
        let _ = args;
        Ok(Value::Bool(false))
    }
}

pub fn rt_iocp_deregister_interp(args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(target_os = "windows")]
    {
        let loop_fd = args.get(0).and_then(|v| v.as_int().ok()).unwrap_or(-1);
        let fd = args.get(1).and_then(|v| v.as_int().ok()).unwrap_or(-1);
        return Ok(Value::Bool(platform::deregister(loop_fd, fd)));
    }
    #[cfg(not(target_os = "windows"))]
    {
        let _ = args;
        Ok(Value::Bool(false))
    }
}

pub fn rt_iocp_poll_interp(args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(target_os = "windows")]
    {
        let loop_fd = args.get(0).and_then(|v| v.as_int().ok()).unwrap_or(-1);
        let max_events = args.get(1).and_then(|v| v.as_int().ok()).unwrap_or(64);
        let timeout_ms = args.get(2).and_then(|v| v.as_int().ok()).unwrap_or(-1);
        return Ok(Value::array(platform::poll(loop_fd, max_events, timeout_ms)));
    }
    #[cfg(not(target_os = "windows"))]
    {
        let _ = args;
        Ok(Value::array(vec![]))
    }
}

pub fn rt_iocp_close_interp(args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(target_os = "windows")]
    {
        let loop_fd = args.get(0).and_then(|v| v.as_int().ok()).unwrap_or(-1);
        return Ok(Value::Bool(platform::close(loop_fd)));
    }
    #[cfg(not(target_os = "windows"))]
    {
        let _ = args;
        Ok(Value::Bool(false))
    }
}

// ---- event ports ----

pub fn rt_event_ports_create_interp(_args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(any(target_os = "solaris", target_os = "illumos"))]
    { return Ok(Value::Int(platform::create())); }
    #[cfg(not(any(target_os = "solaris", target_os = "illumos")))]
    { Ok(Value::Int(-1)) }
}

pub fn rt_event_ports_register_interp(args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(any(target_os = "solaris", target_os = "illumos"))]
    {
        let loop_fd = args.get(0).and_then(|v| v.as_int().ok()).unwrap_or(-1);
        let fd = args.get(1).and_then(|v| v.as_int().ok()).unwrap_or(-1);
        let interest = args.get(2).and_then(|v| v.as_int().ok()).unwrap_or(0);
        let token = args.get(3).and_then(|v| v.as_int().ok()).unwrap_or(0);
        let edge = args.get(4).map(|v| v.truthy()).unwrap_or(false);
        return Ok(Value::Bool(platform::register(loop_fd, fd, interest, token, edge)));
    }
    #[cfg(not(any(target_os = "solaris", target_os = "illumos")))]
    {
        let _ = args;
        Ok(Value::Bool(false))
    }
}

pub fn rt_event_ports_deregister_interp(args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(any(target_os = "solaris", target_os = "illumos"))]
    {
        let loop_fd = args.get(0).and_then(|v| v.as_int().ok()).unwrap_or(-1);
        let fd = args.get(1).and_then(|v| v.as_int().ok()).unwrap_or(-1);
        return Ok(Value::Bool(platform::deregister(loop_fd, fd)));
    }
    #[cfg(not(any(target_os = "solaris", target_os = "illumos")))]
    {
        let _ = args;
        Ok(Value::Bool(false))
    }
}

pub fn rt_event_ports_poll_interp(args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(any(target_os = "solaris", target_os = "illumos"))]
    {
        let loop_fd = args.get(0).and_then(|v| v.as_int().ok()).unwrap_or(-1);
        let max_events = args.get(1).and_then(|v| v.as_int().ok()).unwrap_or(64);
        let timeout_ms = args.get(2).and_then(|v| v.as_int().ok()).unwrap_or(-1);
        return Ok(Value::array(platform::poll(loop_fd, max_events, timeout_ms)));
    }
    #[cfg(not(any(target_os = "solaris", target_os = "illumos")))]
    {
        let _ = args;
        Ok(Value::array(vec![]))
    }
}

pub fn rt_event_ports_close_interp(args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(any(target_os = "solaris", target_os = "illumos"))]
    {
        let loop_fd = args.get(0).and_then(|v| v.as_int().ok()).unwrap_or(-1);
        return Ok(Value::Bool(platform::close(loop_fd)));
    }
    #[cfg(not(any(target_os = "solaris", target_os = "illumos")))]
    {
        let _ = args;
        Ok(Value::Bool(false))
    }
}
