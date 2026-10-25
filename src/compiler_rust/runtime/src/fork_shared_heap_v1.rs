//! Rust twins of the EXPERIMENTAL MIR fork-worker primitives in
//! src/runtime/runtime_fork.c (`rt_fork_shared_heap_v1`, `rt_fork_shared_heap_wait_v1`).
//!
//! Semantics match the C definition exactly:
//!   >0 parent (child pid)   0 child
//!   -1 fork failed   -2 more than one thread alive   -3 unsupported host
//! On Linux it refuses to fork a multithreaded process (another thread may hold
//! an allocator or stdio lock the child would deadlock on), flushes stdio, and
//! the child dies with the parent via PR_SET_PDEATHSIG(SIGKILL).
//!
//! Link lanes: like the other dual `rt_*` symbols (e.g. `rt_process_wait`), the
//! C and Rust definitions are never both admitted. The ELF link layers the Rust
//! runtime before the core-C archive with `--allow-multiple-definition`
//! (first definition wins; PlatformLinkConfig), MSVC uses `/FORCE:MULTIPLE`,
//! and the dynamic-runtime lane resolves the executable's static copy over the
//! shared object's. This crate's build.rs does not compile runtime_fork.c.
//! Design: doc/05_design/compiler/perf/mir_fork_workers_cow_v1.md

#[cfg(target_os = "linux")]
fn thread_count() -> i64 {
    match std::fs::read_dir("/proc/self/task") {
        Ok(tasks) => tasks
            .filter_map(|e| e.ok())
            .filter(|e| !e.file_name().to_string_lossy().starts_with('.'))
            .count() as i64,
        Err(_) => -1,
    }
}

#[cfg(target_os = "linux")]
#[no_mangle]
pub extern "C" fn rt_fork_shared_heap_v1() -> i64 {
    if thread_count() != 1 {
        return -2;
    }
    unsafe {
        libc::fflush(std::ptr::null_mut());
        let expected_parent = libc::getpid();
        let pid = libc::fork();
        if pid < 0 {
            return -1;
        }
        if pid == 0 {
            if libc::prctl(libc::PR_SET_PDEATHSIG, libc::SIGKILL) != 0 || libc::getppid() != expected_parent {
                libc::_exit(127);
            }
            // Keep the inherited heap registry read-only so the child neither
            // privatizes nor regrows the parent's table.
            crate::value::heap::heap_registry_freeze_for_fork_child();
            return 0;
        }
        pid as i64
    }
}

#[cfg(not(target_os = "linux"))]
#[no_mangle]
pub extern "C" fn rt_fork_shared_heap_v1() -> i64 {
    // No portable single-thread proof or parent-death signal here.
    -3
}

/// Blocking reap of a `rt_fork_shared_heap_v1` child, matching the C lane:
///   >=0 exit status   -(128+signo) killed by a signal   -1 waitpid failed
/// `child_pid <= 0` is refused: waitpid(-1) would reap any child.
/// Bug: doc/08_tracking/bug/mir_fork_wait_returns_before_children_2026-10-24.md
#[cfg(unix)]
#[no_mangle]
pub extern "C" fn rt_fork_shared_heap_wait_v1(child_pid: i64) -> i64 {
    if child_pid <= 0 {
        return -1;
    }
    let mut status: libc::c_int = 0;
    let waited = loop {
        let w = unsafe { libc::waitpid(child_pid as libc::pid_t, &mut status, 0) };
        if w < 0 && std::io::Error::last_os_error().raw_os_error() == Some(libc::EINTR) {
            continue;
        }
        break w;
    };
    if waited < 0 {
        return -1;
    }
    if libc::WIFEXITED(status) {
        return libc::WEXITSTATUS(status) as i64;
    }
    if libc::WIFSIGNALED(status) {
        return -(128 + libc::WTERMSIG(status) as i64);
    }
    -1
}

#[cfg(not(unix))]
#[no_mangle]
pub extern "C" fn rt_fork_shared_heap_wait_v1(_child_pid: i64) -> i64 {
    -1
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;

    #[test]
    fn wait_reports_exit_status_signal_and_refusals() {
        let exited = std::process::Command::new("sh").args(["-c", "exit 7"]).spawn().unwrap();
        assert_eq!(rt_fork_shared_heap_wait_v1(exited.id() as i64), 7);
        let killed = std::process::Command::new("sh").args(["-c", "kill -9 $$"]).spawn().unwrap();
        assert_eq!(rt_fork_shared_heap_wait_v1(killed.id() as i64), -(128 + 9));
        assert_eq!(rt_fork_shared_heap_wait_v1(0), -1);
        assert_eq!(rt_fork_shared_heap_wait_v1(-1), -1);
        // Already reaped: waitpid fails with ECHILD.
        assert_eq!(rt_fork_shared_heap_wait_v1(exited.id() as i64), -1);
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn fork_refuses_a_multithreaded_process() {
        let _t = std::thread::spawn(|| std::thread::sleep(std::time::Duration::from_secs(2)));
        assert_eq!(rt_fork_shared_heap_v1(), -2);
    }
}
