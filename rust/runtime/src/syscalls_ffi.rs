//! Re-export syscall-based FFI functions from ffi_syscalls crate
//!
//! This module provides a bridge between the Simple runtime and the minimal
//! no-std ffi_syscalls crate (11 KB binary with zero external dependencies).
//!
//! These functions use direct POSIX syscalls without any std library overhead,
//! making them ideal for minimal builds and reducing binary size.

// Re-export all syscall functions from ffi_syscalls crate
// These are already marked with #[no_mangle] and extern "C" in the source crate

extern "C" {
    // ============================================
    // File I/O - Direct Syscalls (9 functions)
    // ============================================

    /// Check if file exists using stat() syscall
    pub fn rt_file_exists(path: *const libc::c_char) -> bool;

    /// Read file contents using open()+read()+close() syscalls
    pub fn rt_file_read_text(path: *const libc::c_char) -> *mut libc::c_char;

    /// Write file contents using open(O_CREAT|O_WRONLY)+write()+close()
    pub fn rt_file_write_text(path: *const libc::c_char, content: *const libc::c_char) -> bool;

    /// Delete file using unlink() syscall
    pub fn rt_file_delete(path: *const libc::c_char) -> bool;

    /// Get file size using stat() syscall, returns -1 on error
    pub fn rt_file_size(path: *const libc::c_char) -> i64;

    /// Create directory using mkdir() syscall
    pub fn rt_dir_create(path: *const libc::c_char, recursive: bool) -> bool;

    /// List directory contents using opendir()+readdir()+closedir()
    /// Returns null-terminated array of strings (caller must free)
    pub fn rt_dir_list(path: *const libc::c_char) -> *mut *mut libc::c_char;

    /// Acquire file lock using fcntl(F_SETLK), returns fd or -1
    pub fn rt_file_lock(path: *const libc::c_char) -> i64;

    /// Release file lock using fcntl(F_UNLCK) and close fd
    pub fn rt_file_unlock(fd: i64) -> bool;

    // ============================================
    // File I/O Extended - Direct Syscalls (4 functions)
    // ============================================

    /// Copy file using read()+write() in chunks
    pub fn rt_file_copy(src: *const libc::c_char, dst: *const libc::c_char) -> bool;

    /// Remove file (alias to rt_file_delete)
    pub fn rt_file_remove(path: *const libc::c_char) -> bool;

    /// Get file modification time using stat()->st_mtime
    pub fn rt_file_modified_time(path: *const libc::c_char) -> i64;

    /// Append text to file using open(O_APPEND)+write()
    pub fn rt_file_append_text(path: *const libc::c_char, content: *const libc::c_char) -> bool;

    // ============================================
    // Environment - Direct Syscalls (3 functions)
    // ============================================

    /// Get current working directory using getcwd() syscall
    pub fn rt_env_cwd() -> *mut libc::c_char;

    /// Get environment variable using getenv(), returns empty string if not set
    pub fn rt_env_get(key: *const libc::c_char) -> *mut libc::c_char;

    /// Get home directory using getenv(HOME) or getpwuid()->pw_dir
    pub fn rt_env_home() -> *mut libc::c_char;

    /// Set environment variable using setenv()
    pub fn rt_env_set(key: *const libc::c_char, value: *const libc::c_char) -> bool;

    // ============================================
    // Process - Direct Syscalls (2 functions)
    // ============================================

    /// Get process ID using getpid() syscall
    pub fn rt_getpid() -> i64;

    /// Run process using fork()+execvp()+waitpid(), returns exit code
    pub fn rt_process_run(
        cmd: *const libc::c_char,
        args: *const *const libc::c_char,
        arg_count: libc::size_t,
    ) -> i32;

    // ============================================
    // System Info - Direct Syscalls (2 functions)
    // ============================================

    /// Get CPU count using sysconf(_SC_NPROCESSORS_ONLN)
    pub fn rt_system_cpu_count() -> i64;

    /// Get hostname using gethostname() syscall
    pub fn rt_hostname() -> *mut libc::c_char;

    // ============================================
    // Memory-Mapped File I/O (2 functions)
    // ============================================

    /// Read file as text using mmap() for efficient large file reading
    pub fn rt_file_mmap_read_text(path: *const libc::c_char) -> *mut libc::c_char;

    /// Read file as bytes using mmap() for efficient large file reading
    pub fn rt_file_mmap_read_bytes(path: *const libc::c_char) -> *mut u8;
}

// Safe wrapper functions for convenience (optional)

/// Safe wrapper for rt_file_exists
pub fn file_exists(path: &str) -> bool {
    use std::ffi::CString;
    let c_path = CString::new(path).unwrap();
    unsafe { rt_file_exists(c_path.as_ptr()) }
}

/// Safe wrapper for rt_env_cwd
pub fn get_cwd() -> String {
    use std::ffi::CStr;
    unsafe {
        let ptr = rt_env_cwd();
        if ptr.is_null() {
            return String::new();
        }
        let c_str = CStr::from_ptr(ptr);
        let result = c_str.to_string_lossy().into_owned();
        libc::free(ptr as *mut libc::c_void);
        result
    }
}

/// Safe wrapper for rt_getpid
pub fn get_pid() -> i64 {
    unsafe { rt_getpid() }
}

/// Safe wrapper for rt_system_cpu_count
pub fn get_cpu_count() -> i64 {
    unsafe { rt_system_cpu_count() }
}

/// Safe wrapper for rt_hostname
pub fn get_hostname() -> String {
    use std::ffi::CStr;
    unsafe {
        let ptr = rt_hostname();
        if ptr.is_null() {
            return String::new();
        }
        let c_str = CStr::from_ptr(ptr);
        let result = c_str.to_string_lossy().into_owned();
        libc::free(ptr as *mut libc::c_void);
        result
    }
}

// Note: Unit tests are in test/system/ffi/syscalls_test.spl
// Rust unit tests don't work well with no_std crates due to test framework requirements
