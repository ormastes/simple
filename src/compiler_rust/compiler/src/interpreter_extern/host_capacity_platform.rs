//! Host snapshots shared by the interpreter adapters; independently testable
//! without rebuilding or deploying the bootstrap seed.

#[cfg(windows)]
mod windows {
    #[repr(C)]
    #[derive(Default)]
    struct MemoryStatus {
        length: u32,
        load: u32,
        total_physical: u64,
        available_physical: u64,
        total_page_file: u64,
        available_page_file: u64,
        total_virtual: u64,
        available_virtual: u64,
        available_extended_virtual: u64,
    }

    #[repr(C)]
    #[derive(Default)]
    struct PerformanceInfo {
        size: u32,
        commit_total: usize,
        commit_limit: usize,
        commit_peak: usize,
        physical_total: usize,
        physical_available: usize,
        system_cache: usize,
        kernel_total: usize,
        kernel_paged: usize,
        kernel_nonpaged: usize,
        page_size: usize,
        handles: u32,
        processes: u32,
        threads: u32,
    }

    #[link(name = "kernel32")]
    unsafe extern "system" {
        fn GlobalMemoryStatusEx(status: *mut MemoryStatus) -> i32;
        fn K32GetPerformanceInfo(info: *mut PerformanceInfo, size: u32) -> i32;
        fn GetDiskFreeSpaceExW(path: *const u16, available: *mut u64, total: *mut u64, free: *mut u64) -> i32;
    }

    pub fn memory_headroom() -> i64 {
        let mut status = MemoryStatus {
            length: std::mem::size_of::<MemoryStatus>() as u32,
            ..Default::default()
        };
        if unsafe { GlobalMemoryStatusEx(&mut status) } == 0 {
            return 0;
        }
        if status.available_physical > i64::MAX as u64 || status.available_page_file > i64::MAX as u64 {
            return 0;
        }
        status.available_physical.min(status.available_page_file) as i64
    }

    pub fn commit_headroom() -> i64 {
        let size = std::mem::size_of::<PerformanceInfo>() as u32;
        let mut info = PerformanceInfo {
            size,
            ..Default::default()
        };
        if unsafe { K32GetPerformanceInfo(&mut info, size) } == 0 || info.page_size == 0 {
            return 0;
        }
        info.commit_limit
            .checked_sub(info.commit_total)
            .and_then(|pages| pages.checked_mul(info.page_size))
            .and_then(|bytes| i64::try_from(bytes).ok())
            .unwrap_or(0)
    }

    pub fn disk_headroom(path: &str) -> i64 {
        if path.is_empty() || path.len() >= 4096 || path.contains('\0') {
            return 0;
        }
        let wide: Vec<u16> = path.encode_utf16().chain(std::iter::once(0)).collect();
        let mut available = 0;
        if unsafe {
            GetDiskFreeSpaceExW(
                wide.as_ptr(),
                &mut available,
                std::ptr::null_mut(),
                std::ptr::null_mut(),
            )
        } == 0
        {
            return 0;
        }
        i64::try_from(available).unwrap_or(0)
    }
}

#[cfg(windows)]
pub use windows::{memory_headroom, commit_headroom, disk_headroom};

#[cfg(not(windows))]
pub fn memory_headroom() -> i64 {
    0
}
#[cfg(not(windows))]
pub fn commit_headroom() -> i64 {
    0
}
#[cfg(not(windows))]
pub fn disk_headroom(_path: &str) -> i64 {
    0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn disk_invalid_paths_fail_closed() {
        for path in ["", "\0", "missing-capacity-volume-849fae:\\"] {
            assert_eq!(disk_headroom(path), 0, "path: {path:?}");
        }
        assert_eq!(disk_headroom(&"x".repeat(4096)), 0);
    }

    #[cfg(windows)]
    #[test]
    fn windows_snapshots_report_real_capacity() {
        assert!(memory_headroom() > 0);
        assert!(commit_headroom() > 0);
        let path = std::env::current_dir().unwrap();
        assert!(disk_headroom(path.to_str().unwrap()) > 0);
    }

    #[cfg(windows)]
    #[test]
    fn windows_disk_snapshot_preserves_unicode() {
        let path = std::env::temp_dir().join(format!("simple-capacity-한글-{}", std::process::id()));
        std::fs::create_dir_all(&path).unwrap();
        let available = disk_headroom(path.to_str().unwrap());
        std::fs::remove_dir(&path).unwrap();
        assert!(available > 0);
    }

    #[cfg(not(windows))]
    #[test]
    fn unsupported_platform_returns_unavailable() {
        assert_eq!(memory_headroom(), 0);
        assert_eq!(commit_headroom(), 0);
        assert_eq!(disk_headroom("."), 0);
    }
}
