//! Peak RSS of the child reaped by the most recent bounded/timeout process run.
//!
//! Rust twin of the C runtime's `rt_process_last_child_peak_rss_kib`
//! (runtime_process.c). The value is captured at the child's own reap:
//! unix uses `wait4()` `ru_maxrss` (KiB on Linux/FreeBSD, bytes on macOS),
//! Windows reads `PeakWorkingSetSize` from the still-open child handle.
//! `-1` means "not measured" (never `0`, which is indistinguishable from a
//! real tiny peak).

use std::cell::Cell;

thread_local! {
    static LAST_CHILD_PEAK_RSS_KIB: Cell<i64> = const { Cell::new(-1) };
}

/// Forget the previous measurement; call before spawning a new child.
pub fn reset() {
    LAST_CHILD_PEAK_RSS_KIB.with(|cell| cell.set(-1));
}

fn record(kib: i64) {
    LAST_CHILD_PEAK_RSS_KIB.with(|cell| cell.set(kib));
}

/// Peak RSS in KiB of the last child reaped on this thread, or -1.
#[no_mangle]
pub extern "C" fn rt_process_last_child_peak_rss_kib() -> i64 {
    LAST_CHILD_PEAK_RSS_KIB.with(|cell| cell.get())
}

/// Reap `child` with `wait4`, recording its peak RSS. `nohang` mirrors
/// `try_wait` (`Ok(None)` = still running); otherwise blocks like `wait`.
/// Replaces `Child::try_wait`/`wait` so the rusage is not lost.
#[cfg(unix)]
pub fn reap(child: &mut std::process::Child, nohang: bool) -> std::io::Result<Option<std::process::ExitStatus>> {
    use std::os::unix::process::ExitStatusExt;
    let pid = child.id() as libc::pid_t;
    loop {
        let mut raw_status: libc::c_int = 0;
        let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
        let options = if nohang { libc::WNOHANG } else { 0 };
        let waited = unsafe { libc::wait4(pid, &mut raw_status, options, &mut usage) };
        if waited < 0 {
            let error = std::io::Error::last_os_error();
            if error.kind() == std::io::ErrorKind::Interrupted {
                continue;
            }
            return Err(error);
        }
        if waited == 0 {
            return Ok(None);
        }
        let max_rss = usage.ru_maxrss as i64;
        #[cfg(target_os = "macos")]
        let kib = max_rss / 1024; // bytes on Darwin
        #[cfg(not(target_os = "macos"))]
        let kib = max_rss;
        record(if kib > 0 { kib } else { -1 });
        return Ok(Some(std::process::ExitStatus::from_raw(raw_status)));
    }
}

/// Windows: `Child::try_wait`/`wait` plus the child's peak working set, read
/// while std still owns the (open) process handle.
#[cfg(windows)]
pub fn reap(child: &mut std::process::Child, nohang: bool) -> std::io::Result<Option<std::process::ExitStatus>> {
    let status = if nohang { child.try_wait()? } else { Some(child.wait()?) };
    if status.is_some() {
        record(windows_peak_working_set_kib(child));
    }
    Ok(status)
}

#[cfg(windows)]
fn windows_peak_working_set_kib(child: &std::process::Child) -> i64 {
    use std::os::windows::io::AsRawHandle;
    use windows_sys::Win32::System::ProcessStatus::{K32GetProcessMemoryInfo, PROCESS_MEMORY_COUNTERS};
    let mut counters = PROCESS_MEMORY_COUNTERS {
        cb: std::mem::size_of::<PROCESS_MEMORY_COUNTERS>() as u32,
        ..unsafe { std::mem::zeroed() }
    };
    let ok = unsafe { K32GetProcessMemoryInfo(child.as_raw_handle() as *mut _, &mut counters, counters.cb) };
    if ok != 0 && counters.PeakWorkingSetSize > 0 {
        (counters.PeakWorkingSetSize / 1024) as i64
    } else {
        -1
    }
}

#[cfg(not(any(unix, windows)))]
pub fn reap(child: &mut std::process::Child, nohang: bool) -> std::io::Result<Option<std::process::ExitStatus>> {
    if nohang { child.try_wait() } else { child.wait().map(Some) }
}
