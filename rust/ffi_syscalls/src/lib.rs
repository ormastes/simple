#![cfg_attr(not(test), no_std)]
#![allow(non_camel_case_types)]

// Only libc for raw syscall types - no std library (except in test mode)
extern crate libc;

use core::ptr;

#[cfg(not(test))]
use core::panic::PanicInfo;

// Panic handler required for no_std (not needed in test mode)
#[cfg(not(test))]
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    unsafe {
        libc::abort();
    }
}

// ============================================
// File I/O - Direct Syscalls (9 functions)
// ============================================

#[no_mangle]
pub unsafe extern "C" fn rt_file_exists(path: *const libc::c_char) -> bool {
    let mut stat_buf: libc::stat = core::mem::zeroed();
    libc::stat(path, &mut stat_buf) == 0
}

#[no_mangle]
pub unsafe extern "C" fn rt_file_read_text(path: *const libc::c_char) -> *mut libc::c_char {
    let fd = libc::open(path, libc::O_RDONLY);
    if fd < 0 { return ptr::null_mut(); }

    // Get file size
    let mut stat_buf: libc::stat = core::mem::zeroed();
    if libc::fstat(fd, &mut stat_buf) < 0 {
        libc::close(fd);
        return ptr::null_mut();
    }
    let size = stat_buf.st_size as usize;

    // Allocate buffer
    let buf = libc::malloc(size + 1) as *mut u8;
    if buf.is_null() {
        libc::close(fd);
        return ptr::null_mut();
    }

    // Read file
    let bytes_read = libc::read(fd, buf as *mut libc::c_void, size);
    libc::close(fd);

    if bytes_read < 0 {
        libc::free(buf as *mut libc::c_void);
        return ptr::null_mut();
    }

    // Null terminate
    *buf.add(bytes_read as usize) = 0;
    buf as *mut libc::c_char
}

#[no_mangle]
pub unsafe extern "C" fn rt_file_write_text(
    path: *const libc::c_char,
    content: *const libc::c_char
) -> bool {
    let fd = libc::open(
        path,
        libc::O_WRONLY | libc::O_CREAT | libc::O_TRUNC,
        0o644
    );
    if fd < 0 { return false; }

    let len = libc::strlen(content);
    let written = libc::write(fd, content as *const libc::c_void, len);
    libc::close(fd);

    written as usize == len
}

#[no_mangle]
pub unsafe extern "C" fn rt_file_delete(path: *const libc::c_char) -> bool {
    libc::unlink(path) == 0
}

#[no_mangle]
pub unsafe extern "C" fn rt_file_size(path: *const libc::c_char) -> i64 {
    let mut stat_buf: libc::stat = core::mem::zeroed();
    if libc::stat(path, &mut stat_buf) < 0 {
        return -1;
    }
    stat_buf.st_size as i64
}

#[no_mangle]
pub unsafe extern "C" fn rt_dir_create(path: *const libc::c_char, recursive: bool) -> bool {
    if recursive {
        // TODO: Implement recursive mkdir by parsing path components
        // For now, only support non-recursive mode
        false
    } else {
        libc::mkdir(path, 0o755) == 0
    }
}

#[no_mangle]
pub unsafe extern "C" fn rt_dir_list(path: *const libc::c_char) -> *mut *mut libc::c_char {
    let dir = libc::opendir(path);
    if dir.is_null() { return ptr::null_mut(); }

    // Count entries first (excluding . and ..)
    let mut count = 0;
    loop {
        let entry = libc::readdir(dir);
        if entry.is_null() { break; }

        let name_ptr = (*entry).d_name.as_ptr();
        let name = core::ffi::CStr::from_ptr(name_ptr);

        // Skip . and ..
        if name.to_bytes() == b"." || name.to_bytes() == b".." {
            continue;
        }
        count += 1;
    }

    // Rewind and collect
    libc::rewinddir(dir);
    let array = libc::malloc((count + 1) * core::mem::size_of::<*mut libc::c_char>())
        as *mut *mut libc::c_char;

    if array.is_null() {
        libc::closedir(dir);
        return ptr::null_mut();
    }

    let mut i = 0;
    loop {
        let entry = libc::readdir(dir);
        if entry.is_null() { break; }

        let name_ptr = (*entry).d_name.as_ptr();
        let name = core::ffi::CStr::from_ptr(name_ptr);

        // Skip . and ..
        if name.to_bytes() == b"." || name.to_bytes() == b".." {
            continue;
        }

        let name_len = libc::strlen(name_ptr);
        let name_copy = libc::malloc(name_len + 1) as *mut libc::c_char;
        if !name_copy.is_null() {
            libc::strcpy(name_copy, name_ptr);
            *array.add(i) = name_copy;
            i += 1;
        }
    }
    *array.add(count) = ptr::null_mut(); // Null terminate array

    libc::closedir(dir);
    array
}

#[no_mangle]
pub unsafe extern "C" fn rt_file_lock(path: *const libc::c_char) -> i64 {
    let fd = libc::open(path, libc::O_RDWR);
    if fd < 0 { return -1; }

    let mut lock: libc::flock = core::mem::zeroed();
    lock.l_type = libc::F_WRLCK as i16;
    lock.l_whence = libc::SEEK_SET as i16;
    lock.l_start = 0;
    lock.l_len = 0; // Lock entire file

    if libc::fcntl(fd, libc::F_SETLK, &lock) < 0 {
        libc::close(fd);
        return -1;
    }

    fd as i64
}

#[no_mangle]
pub unsafe extern "C" fn rt_file_unlock(fd: i64) -> bool {
    let mut lock: libc::flock = core::mem::zeroed();
    lock.l_type = libc::F_UNLCK as i16;
    lock.l_whence = libc::SEEK_SET as i16;
    lock.l_start = 0;
    lock.l_len = 0;

    let result = libc::fcntl(fd as libc::c_int, libc::F_SETLK, &lock);
    libc::close(fd as libc::c_int);
    result == 0
}

// ============================================
// File I/O Extended - Direct Syscalls (4 functions)
// ============================================

#[no_mangle]
pub unsafe extern "C" fn rt_file_copy(src: *const libc::c_char, dst: *const libc::c_char) -> bool {
    // Open source file
    let src_fd = libc::open(src, libc::O_RDONLY);
    if src_fd < 0 { return false; }

    // Get source file size
    let mut stat_buf: libc::stat = core::mem::zeroed();
    if libc::fstat(src_fd, &mut stat_buf) < 0 {
        libc::close(src_fd);
        return false;
    }
    let size = stat_buf.st_size as usize;

    // Open destination file
    let dst_fd = libc::open(
        dst,
        libc::O_WRONLY | libc::O_CREAT | libc::O_TRUNC,
        stat_buf.st_mode as libc::c_int
    );
    if dst_fd < 0 {
        libc::close(src_fd);
        return false;
    }

    // Allocate buffer for copy
    let buf = libc::malloc(8192) as *mut u8;
    if buf.is_null() {
        libc::close(src_fd);
        libc::close(dst_fd);
        return false;
    }

    // Copy file contents
    let mut success = true;
    let mut remaining = size;
    while remaining > 0 {
        let to_read = if remaining > 8192 { 8192 } else { remaining };
        let bytes_read = libc::read(src_fd, buf as *mut libc::c_void, to_read);

        if bytes_read <= 0 {
            success = false;
            break;
        }

        let bytes_written = libc::write(dst_fd, buf as *const libc::c_void, bytes_read as usize);
        if bytes_written != bytes_read {
            success = false;
            break;
        }

        remaining -= bytes_read as usize;
    }

    // Cleanup
    libc::free(buf as *mut libc::c_void);
    libc::close(src_fd);
    libc::close(dst_fd);

    success
}

#[no_mangle]
pub unsafe extern "C" fn rt_file_remove(path: *const libc::c_char) -> bool {
    // Alias to rt_file_delete (same as unlink())
    libc::unlink(path) == 0
}

#[no_mangle]
pub unsafe extern "C" fn rt_file_modified_time(path: *const libc::c_char) -> i64 {
    let mut stat_buf: libc::stat = core::mem::zeroed();
    if libc::stat(path, &mut stat_buf) < 0 {
        return -1;
    }
    stat_buf.st_mtime as i64
}

#[no_mangle]
pub unsafe extern "C" fn rt_file_append_text(
    path: *const libc::c_char,
    content: *const libc::c_char
) -> bool {
    let fd = libc::open(
        path,
        libc::O_WRONLY | libc::O_CREAT | libc::O_APPEND,
        0o644
    );
    if fd < 0 { return false; }

    let len = libc::strlen(content);
    let written = libc::write(fd, content as *const libc::c_void, len);
    libc::close(fd);

    written as usize == len
}

// ============================================
// Environment - Direct Syscalls (3 functions)
// ============================================

#[no_mangle]
pub unsafe extern "C" fn rt_env_cwd() -> *mut libc::c_char {
    let buf = libc::malloc(4096) as *mut libc::c_char;
    if buf.is_null() { return ptr::null_mut(); }

    if libc::getcwd(buf, 4096).is_null() {
        libc::free(buf as *mut libc::c_void);
        return ptr::null_mut();
    }
    buf
}

#[no_mangle]
pub unsafe extern "C" fn rt_env_get(key: *const libc::c_char) -> *mut libc::c_char {
    let value = libc::getenv(key);
    if value.is_null() {
        // Return empty string instead of null
        let empty = libc::malloc(1) as *mut libc::c_char;
        if !empty.is_null() {
            *empty = 0;
        }
        return empty;
    }

    let len = libc::strlen(value);
    let copy = libc::malloc(len + 1) as *mut libc::c_char;
    if !copy.is_null() {
        libc::strcpy(copy, value);
    }
    copy
}

#[no_mangle]
pub unsafe extern "C" fn rt_env_home() -> *mut libc::c_char {
    // Try $HOME first
    let home_key = b"HOME\0".as_ptr() as *const libc::c_char;
    let home_val = libc::getenv(home_key);
    if !home_val.is_null() {
        let len = libc::strlen(home_val);
        let copy = libc::malloc(len + 1) as *mut libc::c_char;
        if !copy.is_null() {
            libc::strcpy(copy, home_val);
        }
        return copy;
    }

    // Fallback to getpwuid
    let uid = libc::getuid();
    let pw = libc::getpwuid(uid);
    if pw.is_null() || (*pw).pw_dir.is_null() {
        // Return empty string if not found
        let empty = libc::malloc(1) as *mut libc::c_char;
        if !empty.is_null() {
            *empty = 0;
        }
        return empty;
    }

    let dir = (*pw).pw_dir;
    let len = libc::strlen(dir);
    let copy = libc::malloc(len + 1) as *mut libc::c_char;
    if !copy.is_null() {
        libc::strcpy(copy, dir);
    }
    copy
}

#[no_mangle]
pub unsafe extern "C" fn rt_env_set(
    key: *const libc::c_char,
    value: *const libc::c_char
) -> bool {
    libc::setenv(key, value, 1) == 0
}

// ============================================
// Process - Direct Syscalls (2 functions)
// ============================================

#[no_mangle]
pub unsafe extern "C" fn rt_getpid() -> i64 {
    libc::getpid() as i64
}

#[no_mangle]
pub unsafe extern "C" fn rt_process_run(
    cmd: *const libc::c_char,
    args: *const *const libc::c_char,
    arg_count: libc::size_t
) -> i32 {
    let pid = libc::fork();

    if pid < 0 {
        return -1; // Fork failed
    }

    if pid == 0 {
        // Child process
        let argv = libc::malloc((arg_count + 2) * core::mem::size_of::<*const libc::c_char>())
            as *mut *const libc::c_char;
        if argv.is_null() {
            libc::exit(127);
        }

        *argv = cmd;
        for i in 0..arg_count {
            *argv.add(i + 1) = *args.add(i);
        }
        *argv.add(arg_count + 1) = ptr::null();

        libc::execvp(cmd, argv);
        libc::exit(127); // exec failed
    } else {
        // Parent process
        let mut status: libc::c_int = 0;
        libc::waitpid(pid, &mut status, 0);

        if libc::WIFEXITED(status) {
            libc::WEXITSTATUS(status)
        } else {
            -1
        }
    }
}

// ============================================
// System Info - Direct Syscalls (2 functions)
// ============================================

#[no_mangle]
pub unsafe extern "C" fn rt_system_cpu_count() -> i64 {
    libc::sysconf(libc::_SC_NPROCESSORS_ONLN) as i64
}

#[no_mangle]
pub unsafe extern "C" fn rt_hostname() -> *mut libc::c_char {
    let buf = libc::malloc(256) as *mut libc::c_char;
    if buf.is_null() { return ptr::null_mut(); }

    if libc::gethostname(buf, 256) < 0 {
        libc::free(buf as *mut libc::c_void);
        return ptr::null_mut();
    }
    buf
}

// ============================================
// Memory-Mapped File I/O (2 functions)
// ============================================

/// Read entire file as text using memory-mapping
///
/// Uses mmap() for efficient large file reading (zero-copy)
#[no_mangle]
pub unsafe extern "C" fn rt_file_mmap_read_text(path: *const libc::c_char) -> *mut libc::c_char {
    // Open file
    let fd = libc::open(path, libc::O_RDONLY);
    if fd < 0 {
        return ptr::null_mut();
    }

    // Get file size
    let mut stat_buf: libc::stat = core::mem::zeroed();
    if libc::fstat(fd, &mut stat_buf) < 0 {
        libc::close(fd);
        return ptr::null_mut();
    }
    let size = stat_buf.st_size as usize;

    if size == 0 {
        libc::close(fd);
        // Return empty string
        let empty = libc::malloc(1) as *mut libc::c_char;
        if !empty.is_null() {
            *empty = 0;
        }
        return empty;
    }

    // Memory map the file
    let mapped = libc::mmap(
        ptr::null_mut(),
        size,
        libc::PROT_READ,
        libc::MAP_PRIVATE,
        fd,
        0,
    );

    libc::close(fd); // Can close fd after mmap

    if mapped == libc::MAP_FAILED {
        return ptr::null_mut();
    }

    // Allocate buffer for string copy
    let buf = libc::malloc(size + 1) as *mut libc::c_char;
    if buf.is_null() {
        libc::munmap(mapped, size);
        return ptr::null_mut();
    }

    // Copy from mmap to buffer
    libc::memcpy(buf as *mut libc::c_void, mapped, size);
    *buf.add(size) = 0; // Null terminate

    // Unmap the file
    libc::munmap(mapped, size);

    buf
}

/// Read entire file as bytes using memory-mapping
///
/// Returns pointer to byte array (not null-terminated)
/// Caller must free with rt_free()
#[no_mangle]
pub unsafe extern "C" fn rt_file_mmap_read_bytes(path: *const libc::c_char) -> *mut u8 {
    // Open file
    let fd = libc::open(path, libc::O_RDONLY);
    if fd < 0 {
        return ptr::null_mut();
    }

    // Get file size
    let mut stat_buf: libc::stat = core::mem::zeroed();
    if libc::fstat(fd, &mut stat_buf) < 0 {
        libc::close(fd);
        return ptr::null_mut();
    }
    let size = stat_buf.st_size as usize;

    if size == 0 {
        libc::close(fd);
        // Return empty buffer
        return libc::malloc(0) as *mut u8;
    }

    // Memory map the file
    let mapped = libc::mmap(
        ptr::null_mut(),
        size,
        libc::PROT_READ,
        libc::MAP_PRIVATE,
        fd,
        0,
    );

    libc::close(fd); // Can close fd after mmap

    if mapped == libc::MAP_FAILED {
        return ptr::null_mut();
    }

    // Allocate buffer for byte copy
    let buf = libc::malloc(size) as *mut u8;
    if buf.is_null() {
        libc::munmap(mapped, size);
        return ptr::null_mut();
    }

    // Copy from mmap to buffer
    libc::memcpy(buf as *mut libc::c_void, mapped, size);

    // Unmap the file
    libc::munmap(mapped, size);

    buf
}
