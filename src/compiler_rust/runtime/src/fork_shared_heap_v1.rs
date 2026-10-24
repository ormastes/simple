//! Rust twin of the EXPERIMENTAL MIR fork-worker primitive in
//! src/runtime/runtime_fork.c (`rt_fork_shared_heap_v1`).
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
