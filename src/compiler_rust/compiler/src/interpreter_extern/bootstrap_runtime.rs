//! Interpreter bridges for bootstrap runtime services used by compiler sources.
//! The file and archive operations delegate to the existing native providers so
//! the seed observes the same exclusive-create and descriptor-pinning rules.

use crate::error::CompileError;
use crate::value::Value;
use simple_runtime::RuntimeValue;
use std::ffi::{c_char, CString};

unsafe extern "C" {
    #[link_name = "rt_pinned_archive_open_beneath_v1"]
    fn c_pinned_archive_open_beneath(root: i64, path: i64) -> i64;
    #[link_name = "rt_pinned_archive_device_v1"]
    fn c_pinned_archive_device(handle: i64) -> i64;
    #[link_name = "rt_pinned_archive_inode_v1"]
    fn c_pinned_archive_inode(handle: i64) -> i64;
    #[link_name = "rt_pinned_archive_size_v1"]
    fn c_pinned_archive_size(handle: i64) -> i64;
    #[link_name = "rt_pinned_archive_close_v1"]
    fn c_pinned_archive_close(handle: i64) -> i8;
    #[link_name = "rt_simple_abi_version"]
    fn c_simple_abi_version() -> i64;
    #[link_name = "rt_simple_abi_version_deferred"]
    fn c_simple_abi_version_deferred() -> i64;
    // Session-owned process trees: src/runtime/runtime_process_tree.c, the one
    // implementation for every engine. Return codes: >= 0 success,
    // -errno failure, RT_PTREE_UNSUPPORTED (-100000) when this host has no
    // owner arm (never a silent success); rt_process_kill_tree may also return
    // -100001 (not a session leader) or -100002 (leader reaped, second sweep
    // failed: stop tracking the pid).
    #[link_name = "rt_process_tree_support"]
    fn c_process_tree_support() -> i64;
    #[link_name = "rt_process_spawn_session"]
    fn c_process_spawn_session(cmd: *const c_char, args: *const *const c_char, arg_count: i64) -> i64;
    #[link_name = "rt_process_session_wait"]
    fn c_process_session_wait(pid: i64, timeout_ms: i64) -> i64;
    #[link_name = "rt_process_session_is_running"]
    fn c_process_session_is_running(pid: i64) -> i64;
    #[link_name = "rt_process_kill_session"]
    fn c_process_kill_session(sid: i64, signo: i32) -> i64;
    #[link_name = "rt_process_kill_tree"]
    fn c_process_kill_tree(pid: i64) -> i64;
}

/// Same value as RT_PTREE_UNSUPPORTED in runtime_process_tree.h.
pub const RT_PTREE_UNSUPPORTED: i64 = -100_000;

/// rt_process_tree_support() -> 0 when session ownership works here.
pub fn rt_process_tree_support(args: &[Value]) -> Result<Value, CompileError> {
    if !args.is_empty() {
        return Err(CompileError::runtime("rt_process_tree_support takes no arguments"));
    }
    Ok(Value::Int(unsafe { c_process_tree_support() }))
}

/// rt_process_spawn_session_value(cmd: text, args: [text]) -> pid | -errno |
/// RT_PTREE_UNSUPPORTED. The child is a session leader (pid == sid).
pub fn rt_process_spawn_session_value(args: &[Value]) -> Result<Value, CompileError> {
    let cmd = text_arg(args, 0, "rt_process_spawn_session_value")?;
    let argv: Vec<String> = match args.get(1) {
        Some(Value::Array(items)) => {
            let mut out = Vec::with_capacity(items.len());
            for item in items.iter() {
                let Value::Str(s) = item else {
                    return Err(CompileError::runtime(
                        "rt_process_spawn_session_value: every argument must be text",
                    ));
                };
                out.push(s.as_ref().clone());
            }
            out
        }
        _ => {
            return Err(CompileError::runtime(
                "rt_process_spawn_session_value: argument 1 must be an array of text",
            ))
        }
    };
    let c_cmd = CString::new(cmd).map_err(|_| {
        CompileError::runtime("rt_process_spawn_session_value: cmd contains a NUL byte")
    })?;
    let mut c_args = Vec::with_capacity(argv.len());
    for arg in &argv {
        c_args.push(CString::new(arg.as_str()).map_err(|_| {
            CompileError::runtime("rt_process_spawn_session_value: an argument contains a NUL byte")
        })?);
    }
    let pointers: Vec<*const c_char> = c_args.iter().map(|arg| arg.as_ptr()).collect();
    // c_cmd / c_args outlive the call; the C side copies nothing after exec.
    let pid = unsafe {
        c_process_spawn_session(
            c_cmd.as_ptr(),
            if pointers.is_empty() { std::ptr::null() } else { pointers.as_ptr() },
            pointers.len() as i64,
        )
    };
    Ok(Value::Int(pid))
}

/// rt_process_session_wait(pid, timeout_ms) -> exit code | -(128+signo) | -1 | -2 timeout.
pub fn rt_process_session_wait(args: &[Value]) -> Result<Value, CompileError> {
    let pid = int_arg(args, 0, "rt_process_session_wait")?;
    let timeout_ms = int_arg(args, 1, "rt_process_session_wait")?;
    Ok(Value::Int(unsafe { c_process_session_wait(pid, timeout_ms) }))
}

/// rt_process_session_is_running(pid) -> 1 | 0 | RT_PTREE_UNSUPPORTED.
pub fn rt_process_session_is_running(args: &[Value]) -> Result<Value, CompileError> {
    let pid = int_arg(args, 0, "rt_process_session_is_running")?;
    Ok(Value::Int(unsafe { c_process_session_is_running(pid) }))
}

/// rt_process_kill_session(sid, signo) -> count signalled | -errno | RT_PTREE_UNSUPPORTED.
pub fn rt_process_kill_session(args: &[Value]) -> Result<Value, CompileError> {
    let sid = int_arg(args, 0, "rt_process_kill_session")?;
    let signo = int_arg(args, 1, "rt_process_kill_session")?;
    let signo = i32::try_from(signo)
        .map_err(|_| CompileError::runtime("rt_process_kill_session: signal out of range"))?;
    Ok(Value::Int(unsafe { c_process_kill_session(sid, signo) }))
}

/// rt_process_kill_tree(pid) -> 0 | RT_PTREE_NOT_SESSION_LEADER | -errno | RT_PTREE_UNSUPPORTED.
pub fn rt_process_kill_tree(args: &[Value]) -> Result<Value, CompileError> {
    let pid = int_arg(args, 0, "rt_process_kill_tree")?;
    Ok(Value::Int(unsafe { c_process_kill_tree(pid) }))
}

fn text_arg<'a>(args: &'a [Value], index: usize, name: &str) -> Result<&'a str, CompileError> {
    match args.get(index) {
        Some(Value::Str(value)) => Ok(value.as_str()),
        _ => Err(CompileError::runtime(format!("{name}: argument {index} must be text"))),
    }
}

fn int_arg(args: &[Value], index: usize, name: &str) -> Result<i64, CompileError> {
    match args.get(index) {
        Some(Value::Int(value)) => Ok(*value),
        _ => Err(CompileError::runtime(format!(
            "{name}: argument {index} must be an integer"
        ))),
    }
}

struct RuntimeText(RuntimeValue);

impl RuntimeText {
    fn new(text: &str) -> Self {
        Self(simple_runtime::value::rt_string_new(text.as_ptr(), text.len() as u64))
    }

    fn raw(&self) -> i64 {
        self.0.to_raw() as i64
    }
}

impl Drop for RuntimeText {
    fn drop(&mut self) {
        let _ = simple_runtime::value::rt_string_free(self.0);
    }
}

pub fn rt_file_copy_create_excl_no_follow(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "rt_file_copy_create_excl_no_follow";
    let source = text_arg(args, 0, NAME)?;
    let destination = text_arg(args, 1, NAME)?;
    let ok = unsafe {
        simple_runtime::value::sffi::file_io::file_ops::rt_file_copy_create_excl_no_follow(
            source.as_ptr(),
            source.len() as u64,
            destination.as_ptr(),
            destination.len() as u64,
        )
    };
    Ok(Value::Bool(ok))
}

pub fn rt_file_link_create_excl_no_follow(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "rt_file_link_create_excl_no_follow";
    let source = text_arg(args, 0, NAME)?;
    let destination = text_arg(args, 1, NAME)?;
    let ok = unsafe {
        simple_runtime::value::sffi::file_io::file_ops::rt_file_link_create_excl_no_follow(
            source.as_ptr(),
            source.len() as u64,
            destination.as_ptr(),
            destination.len() as u64,
        )
    };
    Ok(Value::Bool(ok))
}

pub fn rt_pinned_archive_open_beneath_v1(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "rt_pinned_archive_open_beneath_v1";
    let root = RuntimeText::new(text_arg(args, 0, NAME)?);
    let path = RuntimeText::new(text_arg(args, 1, NAME)?);
    Ok(Value::Int(unsafe {
        c_pinned_archive_open_beneath(root.raw(), path.raw())
    }))
}

pub fn rt_pinned_archive_device_v1(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(unsafe {
        c_pinned_archive_device(int_arg(args, 0, "rt_pinned_archive_device_v1")?)
    }))
}

pub fn rt_pinned_archive_inode_v1(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(unsafe {
        c_pinned_archive_inode(int_arg(args, 0, "rt_pinned_archive_inode_v1")?)
    }))
}

pub fn rt_pinned_archive_size_v1(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(unsafe {
        c_pinned_archive_size(int_arg(args, 0, "rt_pinned_archive_size_v1")?)
    }))
}

pub fn rt_pinned_archive_close_v1(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(unsafe {
        c_pinned_archive_close(int_arg(args, 0, "rt_pinned_archive_close_v1")?) != 0
    }))
}

pub fn rt_simple_abi_version(args: &[Value]) -> Result<Value, CompileError> {
    if !args.is_empty() {
        return Err(CompileError::runtime("rt_simple_abi_version takes no arguments"));
    }
    Ok(Value::Int(unsafe { c_simple_abi_version() }))
}

pub fn rt_simple_abi_version_deferred(args: &[Value]) -> Result<Value, CompileError> {
    if !args.is_empty() {
        return Err(CompileError::runtime(
            "rt_simple_abi_version_deferred takes no arguments",
        ));
    }
    Ok(Value::Int(unsafe { c_simple_abi_version_deferred() }))
}

/// Process birth identity must use the same OS unit as the native runtime:
/// Linux /proc start ticks, or Windows FILETIME ticks. Zero means unavailable.
pub fn rt_process_start_identity(args: &[Value]) -> Result<Value, CompileError> {
    let pid = int_arg(args, 0, "rt_process_start_identity")?;
    if pid <= 0 {
        return Ok(Value::Int(0));
    }
    #[cfg(target_os = "linux")]
    {
        let identity = std::fs::read_to_string(format!("/proc/{pid}/stat"))
            .ok()
            .and_then(|stat| {
                let tail = stat.get(stat.rfind(')')? + 2..)?;
                tail.split_whitespace().nth(19)?.parse::<i64>().ok()
            })
            .filter(|identity| *identity > 0)
            .unwrap_or(0);
        return Ok(Value::Int(identity));
    }
    #[cfg(windows)]
    {
        use windows_sys::Win32::Foundation::{CloseHandle, FILETIME};
        use windows_sys::Win32::System::Threading::{GetProcessTimes, OpenProcess, PROCESS_QUERY_LIMITED_INFORMATION};
        if pid > u32::MAX as i64 {
            return Ok(Value::Int(0));
        }
        let process = unsafe { OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, 0, pid as u32) };
        if process.is_null() {
            return Ok(Value::Int(0));
        }
        let mut created: FILETIME = unsafe { std::mem::zeroed() };
        let mut exited: FILETIME = unsafe { std::mem::zeroed() };
        let mut kernel: FILETIME = unsafe { std::mem::zeroed() };
        let mut user: FILETIME = unsafe { std::mem::zeroed() };
        let ok = unsafe { GetProcessTimes(process, &mut created, &mut exited, &mut kernel, &mut user) } != 0;
        unsafe { CloseHandle(process) };
        if !ok {
            return Ok(Value::Int(0));
        }
        let identity = ((created.dwHighDateTime as u64) << 32) | created.dwLowDateTime as u64;
        return Ok(Value::Int(i64::try_from(identity).unwrap_or(0)));
    }
    #[cfg(not(any(target_os = "linux", windows)))]
    Ok(Value::Int(0))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn text(value: &str) -> Value {
        Value::text(value.to_owned())
    }

    #[test]
    fn abi_version_comes_from_the_selected_runtime() {
        let Value::Int(version) = rt_simple_abi_version(&[]).unwrap() else {
            panic!("version type")
        };
        let Value::Int(deferred) = rt_simple_abi_version_deferred(&[]).unwrap() else {
            panic!("deferred type")
        };
        assert!((version == 0 && deferred == 1) || (version > 0 && deferred == 0));
    }

    /// Conformance for the session-owner contract through the interpreter
    /// bridges: an owned session leader, killed as a tree, is not running
    /// afterwards, its escaped grandchild (own process group, reparented) is
    /// gone, and the leader's wait returns at once.
    #[cfg(any(target_os = "linux", target_os = "macos", target_os = "freebsd"))]
    #[test]
    fn session_owner_kills_an_escaped_grandchild_and_reaps_the_leader() {
        assert_eq!(rt_process_tree_support(&[]).unwrap(), Value::Int(0));
        let dir = tempfile::tempdir().unwrap();
        let pidfile = dir.path().join("grandchild.pid");
        let script = "(set -m; sleep 300 & echo $! > \"$1\"); exec sleep 300";
        let spawned = rt_process_spawn_session_value(&[
            text("/bin/sh"),
            Value::array(vec![text("-c"), text(script), text("owner"), text(&pidfile.to_string_lossy())]),
        ])
        .unwrap();
        let Value::Int(pid) = spawned else { panic!("pid type") };
        assert!(pid > 1, "spawn_session returned {pid}");
        assert_eq!(rt_process_session_is_running(&[Value::Int(pid)]).unwrap(), Value::Int(1));
        let mut grandchild: i64 = 0;
        for _ in 0..100 {
            if let Ok(content) = std::fs::read_to_string(&pidfile) {
                if let Ok(value) = content.trim().parse::<i64>() {
                    grandchild = value;
                    break;
                }
            }
            std::thread::sleep(std::time::Duration::from_millis(50));
        }
        assert!(grandchild > 1, "grandchild pid never recorded");
        let alive = |p: i64| unsafe { libc::kill(p as libc::pid_t, 0) == 0 };
        assert!(alive(grandchild));
        assert_eq!(rt_process_session_wait(&[Value::Int(pid), Value::Int(50)]).unwrap(), Value::Int(-2));
        // A live pid that is not a session leader is refused, nothing is signalled.
        assert_eq!(rt_process_kill_tree(&[Value::Int(grandchild)]).unwrap(), Value::Int(-100_001));
        assert!(alive(grandchild));

        assert_eq!(rt_process_kill_tree(&[Value::Int(pid)]).unwrap(), Value::Int(0));
        let mut gone = false;
        for _ in 0..50 {
            if !alive(grandchild) {
                gone = true;
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(20));
        }
        if !gone {
            unsafe { libc::kill(grandchild as libc::pid_t, libc::SIGKILL) };
        }
        assert!(gone, "escaped grandchild survived kill_tree");
        assert_eq!(rt_process_session_is_running(&[Value::Int(pid)]).unwrap(), Value::Int(0));
        // kill_tree already reaped the leader: a further wait is -1 (ECHILD).
        assert_eq!(rt_process_session_wait(&[Value::Int(pid), Value::Int(100)]).unwrap(), Value::Int(-1));
        // An exec failure is -errno, never a pid.
        let bad = rt_process_spawn_session_value(&[text("/nonexistent/never-here"), Value::array(vec![])]).unwrap();
        assert_eq!(bad, Value::Int(-(libc::ENOENT as i64)));
    }

    #[cfg(any(target_os = "linux", windows))]
    #[test]
    fn process_start_identity_is_stable_for_the_current_process() {
        let pid = Value::Int(std::process::id() as i64);
        let first = rt_process_start_identity(&[pid.clone()]).unwrap();
        assert!(matches!(first, Value::Int(value) if value > 0));
        assert_eq!(first, rt_process_start_identity(&[pid]).unwrap());
    }

    #[cfg(unix)]
    #[test]
    fn secure_file_and_pinned_archive_handlers_use_native_contracts() {
        let dir = tempfile::tempdir().unwrap();
        let source = dir.path().join("source");
        let copy = dir.path().join("copy");
        let link = dir.path().join("link");
        std::fs::write(&source, b"archive").unwrap();
        let source = text(&source.to_string_lossy());
        let copy_arg = text(&copy.to_string_lossy());
        let link_arg = text(&link.to_string_lossy());
        assert_eq!(
            rt_file_copy_create_excl_no_follow(&[source.clone(), copy_arg.clone()]).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            rt_file_copy_create_excl_no_follow(&[source.clone(), copy_arg]).unwrap(),
            Value::Bool(false)
        );
        assert_eq!(
            rt_file_link_create_excl_no_follow(&[source, link_arg.clone()]).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            rt_file_link_create_excl_no_follow(&[text(&copy.to_string_lossy()), link_arg]).unwrap(),
            Value::Bool(false)
        );

        let root = text(&dir.path().to_string_lossy());
        let Value::Int(handle) = rt_pinned_archive_open_beneath_v1(&[root, text("copy")]).unwrap() else {
            panic!("handle type")
        };
        assert!(handle > 0);
        assert_eq!(rt_pinned_archive_size_v1(&[Value::Int(handle)]).unwrap(), Value::Int(7));
        assert!(matches!(rt_pinned_archive_device_v1(&[Value::Int(handle)]).unwrap(), Value::Int(value) if value >= 0));
        assert!(matches!(rt_pinned_archive_inode_v1(&[Value::Int(handle)]).unwrap(), Value::Int(value) if value >= 0));
        assert_eq!(
            rt_pinned_archive_close_v1(&[Value::Int(handle)]).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            rt_pinned_archive_size_v1(&[Value::Int(handle)]).unwrap(),
            Value::Int(-1)
        );
    }
}
