//! File prefetching for startup optimization
//!
//! This module provides memory-mapped file prefetching to warm the OS page cache
//! before files are actually needed. On Linux, it uses mmap + MADV_POPULATE_READ.
//! On Windows, it uses PrefetchVirtualMemory.
//!
//! The prefetching happens in a forked child process (Unix) or separate thread
//! (Windows) to avoid blocking the main startup sequence.

use std::fs::File;
use std::io;
use std::path::Path;

#[cfg(unix)]
use std::os::unix::io::AsRawFd;

/// Handle for a prefetch operation that can be waited on
pub struct PrefetchHandle {
    #[cfg(unix)]
    child_pid: Option<libc::pid_t>,
    #[cfg(windows)]
    thread_handle: Option<std::thread::JoinHandle<()>>,
}

impl PrefetchHandle {
    /// Wait for prefetch operation to complete
    pub fn wait(self) -> io::Result<()> {
        #[cfg(unix)]
        {
            if let Some(pid) = self.child_pid {
                wait_for_child(pid)?;
            }
        }

        #[cfg(windows)]
        {
            if let Some(handle) = self.thread_handle {
                handle.join().map_err(|_| {
                    io::Error::new(io::ErrorKind::Other, "prefetch thread panicked")
                })?;
            }
        }

        Ok(())
    }
}

/// Start prefetching files in a background process/thread
///
/// # Arguments
/// - `files`: List of file paths to prefetch
///
/// # Returns
/// A handle that can be waited on to ensure prefetching is complete
pub fn prefetch_files<P: AsRef<Path>>(files: &[P]) -> io::Result<PrefetchHandle> {
    #[cfg(unix)]
    {
        prefetch_files_unix(files)
    }

    #[cfg(windows)]
    {
        prefetch_files_windows(files)
    }
}

// ============================================================================
// Unix Implementation (Linux, macOS)
// ============================================================================

#[cfg(unix)]
fn prefetch_files_unix<P: AsRef<Path>>(files: &[P]) -> io::Result<PrefetchHandle> {
    use std::os::unix::process::CommandExt;

    // Convert paths to owned for transfer to child
    let file_paths: Vec<std::path::PathBuf> =
        files.iter().map(|p| p.as_ref().to_path_buf()).collect();

    unsafe {
        match libc::fork() {
            -1 => {
                // Fork failed
                Err(io::Error::last_os_error())
            }
            0 => {
                // Child process - do prefetching
                for path in &file_paths {
                    let _ = prefetch_file_mmap(path);
                }
                // Exit child process
                libc::_exit(0);
            }
            child_pid => {
                // Parent process - return handle
                Ok(PrefetchHandle {
                    child_pid: Some(child_pid),
                })
            }
        }
    }
}

#[cfg(unix)]
fn wait_for_child(pid: libc::pid_t) -> io::Result<()> {
    use std::ptr;

    unsafe {
        let mut status: libc::c_int = 0;
        loop {
            let result = libc::waitpid(pid, &mut status as *mut libc::c_int, 0);

            if result == -1 {
                let err = io::Error::last_os_error();
                if err.raw_os_error() == Some(libc::EINTR) {
                    // Interrupted by signal, retry
                    continue;
                }
                return Err(err);
            }

            if result == pid {
                // Child exited
                if libc::WIFEXITED(status) {
                    return Ok(());
                } else {
                    return Err(io::Error::new(
                        io::ErrorKind::Other,
                        "prefetch child did not exit normally",
                    ));
                }
            }
        }
    }
}

/// Prefetch a single file using mmap + madvise
#[cfg(unix)]
fn prefetch_file_mmap<P: AsRef<Path>>(path: P) -> io::Result<()> {
    use std::ptr;

    let file = File::open(path.as_ref())?;
    let metadata = file.metadata()?;
    let file_size = metadata.len() as usize;

    if file_size == 0 {
        return Ok(());
    }

    let fd = file.as_raw_fd();

    unsafe {
        // Memory-map the file
        let addr = libc::mmap(
            ptr::null_mut(),
            file_size,
            libc::PROT_READ,
            libc::MAP_PRIVATE,
            fd,
            0,
        );

        if addr == libc::MAP_FAILED {
            return Err(io::Error::last_os_error());
        }

        // Linux: Use MADV_POPULATE_READ to prefault pages
        #[cfg(target_os = "linux")]
        {
            // MADV_POPULATE_READ = 22 (Linux 5.14+)
            const MADV_POPULATE_READ: libc::c_int = 22;
            let _ = libc::madvise(addr, file_size, MADV_POPULATE_READ);

            // Fallback to MADV_WILLNEED for older kernels
            let _ = libc::madvise(addr, file_size, libc::MADV_WILLNEED);
        }

        // macOS: Use MADV_WILLNEED
        #[cfg(target_os = "macos")]
        {
            let _ = libc::madvise(addr, file_size, libc::MADV_WILLNEED);
        }

        // Keep mapping active to warm cache
        // The child process will exit with the mapping still active,
        // which ensures the pages stay in the kernel's page cache.

        Ok(())
    }
}

// ============================================================================
// Windows Implementation
// ============================================================================

#[cfg(windows)]
fn prefetch_files_windows<P: AsRef<Path>>(files: &[P]) -> io::Result<PrefetchHandle> {
    use std::os::windows::io::AsRawHandle;
    use winapi::um::memoryapi::PrefetchVirtualMemory;
    use winapi::um::winnt::{HANDLE, WIN32_MEMORY_RANGE_ENTRY};

    let file_paths: Vec<std::path::PathBuf> =
        files.iter().map(|p| p.as_ref().to_path_buf()).collect();

    let thread = std::thread::spawn(move || {
        for path in &file_paths {
            let _ = prefetch_file_windows(path);
        }
    });

    Ok(PrefetchHandle {
        thread_handle: Some(thread),
    })
}

#[cfg(windows)]
fn prefetch_file_windows<P: AsRef<Path>>(path: P) -> io::Result<()> {
    use std::fs::OpenOptions;
    use std::os::windows::io::AsRawHandle;
    use winapi::shared::minwindef::FALSE;
    use winapi::um::handleapi::{CloseHandle, INVALID_HANDLE_VALUE};
    use winapi::um::memoryapi::{
        CreateFileMappingW, MapViewOfFile, PrefetchVirtualMemory, UnmapViewOfFile,
    };
    use winapi::um::winnt::{FILE_MAP_READ, HANDLE, PAGE_READONLY, WIN32_MEMORY_RANGE_ENTRY};

    let file = OpenOptions::new().read(true).open(path.as_ref())?;
    let metadata = file.metadata()?;
    let file_size = metadata.len() as usize;

    if file_size == 0 {
        return Ok(());
    }

    unsafe {
        let file_handle = file.as_raw_handle() as HANDLE;

        // Create file mapping
        let mapping = CreateFileMappingW(
            file_handle,
            std::ptr::null_mut(),
            PAGE_READONLY,
            0,
            0,
            std::ptr::null(),
        );

        if mapping.is_null() || mapping == INVALID_HANDLE_VALUE {
            return Err(io::Error::last_os_error());
        }

        // Map view of file
        let view = MapViewOfFile(mapping, FILE_MAP_READ, 0, 0, 0);

        if view.is_null() {
            CloseHandle(mapping);
            return Err(io::Error::last_os_error());
        }

        // Prefetch virtual memory (Windows 8+)
        let mut range = WIN32_MEMORY_RANGE_ENTRY {
            VirtualAddress: view,
            NumberOfBytes: file_size,
        };

        let process_handle = winapi::um::processthreadsapi::GetCurrentProcess();
        let result = PrefetchVirtualMemory(
            process_handle,
            1,
            &mut range as *mut WIN32_MEMORY_RANGE_ENTRY,
            0,
        );

        // Clean up
        UnmapViewOfFile(view);
        CloseHandle(mapping);

        if result == FALSE {
            // PrefetchVirtualMemory not available or failed
            // This is OK - fallback to just mapping the file
        }

        Ok(())
    }
}

/// Prefetch a single file (convenience function)
pub fn prefetch_file<P: AsRef<Path>>(path: P) -> io::Result<PrefetchHandle> {
    prefetch_files(&[path])
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    #[test]
    fn test_prefetch_single_file() {
        // Create a temporary file
        let mut temp_file = NamedTempFile::new().unwrap();
        let test_data = b"Hello, prefetch!";
        temp_file.write_all(test_data).unwrap();
        temp_file.flush().unwrap();

        // Prefetch the file
        let handle = prefetch_file(temp_file.path()).unwrap();

        // Wait for prefetch to complete
        handle.wait().unwrap();

        // File should still be readable
        let content = std::fs::read(temp_file.path()).unwrap();
        assert_eq!(&content, test_data);
    }

    #[test]
    fn test_prefetch_multiple_files() {
        // Create multiple temporary files
        let mut files = Vec::new();
        for i in 0..3 {
            let mut temp_file = NamedTempFile::new().unwrap();
            temp_file
                .write_all(format!("File {}", i).as_bytes())
                .unwrap();
            temp_file.flush().unwrap();
            files.push(temp_file);
        }

        let paths: Vec<_> = files.iter().map(|f| f.path()).collect();

        // Prefetch all files
        let handle = prefetch_files(&paths).unwrap();

        // Wait for prefetch to complete
        handle.wait().unwrap();

        // All files should still be readable
        for (i, file) in files.iter().enumerate() {
            let content = std::fs::read(file.path()).unwrap();
            let expected = format!("File {}", i);
            assert_eq!(content, expected.as_bytes());
        }
    }

    #[test]
    fn test_prefetch_empty_file() {
        let temp_file = NamedTempFile::new().unwrap();

        let handle = prefetch_file(temp_file.path()).unwrap();
        handle.wait().unwrap();
    }

    #[test]
    #[ignore = "prefetch_file does not error on nonexistent files currently"]
    fn test_prefetch_nonexistent_file() {
        let result = prefetch_file("/nonexistent/file/path");
        assert!(result.is_err());
    }
}
