//! Tool detection (C compiler, archive tool, linker detection),
//! runtime library discovery, system symbol identification,
//! and LLVM constructor stripping.

use std::path::{Path, PathBuf};

use super::{safe_canonicalize, RUNTIME_PATH_OVERRIDE};

/// Find a C compiler -- delegates to `simple_common::platform::cc_detect`.
pub(crate) fn find_c_compiler() -> String {
    simple_common::platform::cc_detect::find_c_compiler()
}

/// Find an archive tool -- delegates to `simple_common::platform::cc_detect`.
pub(crate) fn find_archive_tool() -> String {
    simple_common::platform::cc_detect::find_archive_tool()
}

pub(crate) fn find_cxx_compiler() -> String {
    simple_common::platform::cc_detect::find_cxx_compiler()
}

/// Find the combined native_all library (runtime + compiler with Cranelift FFI).
pub(crate) fn find_native_all_library() -> Option<PathBuf> {
    if let Some(dir) = RUNTIME_PATH_OVERRIDE.get() {
        let p = dir.join("libsimple_native_all.a");
        if p.exists() {
            return Some(p);
        }
        #[cfg(target_os = "windows")]
        {
            let p = dir.join("simple_native_all.lib");
            if p.exists() {
                return Some(p);
            }
        }
    }

    if let Ok(path) = std::env::var("SIMPLE_NATIVE_ALL_PATH") {
        let p = PathBuf::from(&path);
        if p.exists() {
            return Some(p);
        }
    }
    if let Ok(path) = std::env::var("SIMPLE_RUNTIME_PATH") {
        let p = PathBuf::from(&path).join("libsimple_native_all.a");
        if p.exists() {
            return Some(p);
        }
    }

    let mut candidates: Vec<&str> = vec![
        "src/compiler_rust/target/bootstrap/libsimple_native_all.a",
        "src/compiler_rust/target/release/libsimple_native_all.a",
        "src/compiler_rust/target/debug/libsimple_native_all.a",
    ];

    #[cfg(target_os = "windows")]
    {
        candidates.extend_from_slice(&[
            "src/compiler_rust/target/bootstrap/simple_native_all.lib",
            "src/compiler_rust/target/release/simple_native_all.lib",
            "src/compiler_rust/target/debug/simple_native_all.lib",
        ]);
    }

    for candidate in &candidates {
        let path = PathBuf::from(candidate);
        if path.exists() {
            return Some(path);
        }
    }

    if let Ok(exe) = std::env::current_exe() {
        if let Some(dir) = exe.parent() {
            let path = dir.join("libsimple_native_all.a");
            if path.exists() {
                return Some(path);
            }
            #[cfg(target_os = "windows")]
            {
                let path = dir.join("simple_native_all.lib");
                if path.exists() {
                    return Some(path);
                }
            }
        }
    }

    None
}

/// Find the Simple runtime library.
pub(crate) fn find_runtime_library() -> Option<PathBuf> {
    if let Some(dir) = RUNTIME_PATH_OVERRIDE.get() {
        for name in &["libsimple_runtime.a", "libsimple_native_all.a"] {
            let lib = dir.join(name);
            if lib.exists() {
                return Some(lib);
            }
        }
        #[cfg(target_os = "windows")]
        for name in &["simple_runtime.lib", "simple_native_all.lib"] {
            let lib = dir.join(name);
            if lib.exists() {
                return Some(lib);
            }
        }
    }

    if let Ok(path) = std::env::var("SIMPLE_RUNTIME_PATH") {
        let p = PathBuf::from(&path);
        for name in &["libsimple_runtime.a", "libsimple_native_all.a"] {
            let lib = p.join(name);
            if lib.exists() {
                return Some(lib);
            }
        }
        if p.exists() && p.is_file() {
            return Some(p);
        }
    }

    let mut candidates: Vec<&str> = vec![
        "src/compiler_rust/target/bootstrap/libsimple_runtime.a",
        "src/compiler_rust/target/bootstrap/deps/libsimple_runtime.a",
        "src/compiler_rust/target/release/libsimple_runtime.a",
        "src/compiler_rust/target/release/deps/libsimple_runtime.a",
        "src/compiler_rust/target/debug/libsimple_runtime.a",
        "src/compiler_rust/target/debug/deps/libsimple_runtime.a",
    ];

    #[cfg(target_os = "windows")]
    {
        candidates.extend_from_slice(&[
            "src/compiler_rust/target/bootstrap/simple_runtime.lib",
            "src/compiler_rust/target/bootstrap/deps/simple_runtime.lib",
            "src/compiler_rust/target/release/simple_runtime.lib",
            "src/compiler_rust/target/release/deps/simple_runtime.lib",
            "src/compiler_rust/target/debug/simple_runtime.lib",
            "src/compiler_rust/target/debug/deps/simple_runtime.lib",
        ]);
    }

    #[cfg(not(target_os = "windows"))]
    candidates.push("/usr/local/lib/libsimple_runtime.a");

    for candidate in &candidates {
        let path = PathBuf::from(candidate);
        if path.exists() {
            return Some(path);
        }
    }

    if let Ok(exe) = std::env::current_exe() {
        if let Some(dir) = exe.parent() {
            let path = dir.join("libsimple_runtime.a");
            if path.exists() {
                return Some(path);
            }
            #[cfg(target_os = "windows")]
            {
                let path = dir.join("simple_runtime.lib");
                if path.exists() {
                    return Some(path);
                }
            }
        }
    }

    None
}

/// Find the compiler-rt builtins archive for a freestanding target.
///
/// Clang reports this through `-print-libgcc-file-name`; on Apple toolchains
/// the returned RISC-V path is a compiler-rt archive under the clang resource
/// directory, while ELF cross toolchains may report libgcc instead.
pub(crate) fn find_compiler_rt_builtins(triple: &str) -> Option<PathBuf> {
    let cc = find_c_compiler();
    let output = std::process::Command::new(&cc)
        .arg(format!("--target={}", triple))
        .arg("-print-libgcc-file-name")
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let raw = String::from_utf8_lossy(&output.stdout).trim().to_string();
    if raw.is_empty() {
        return None;
    }
    let path = PathBuf::from(raw);
    if path.exists() && path.is_file() {
        Some(path)
    } else {
        None
    }
}

/// Find an objcopy tool that can handle the host object format.
pub(crate) fn find_objcopy_tool() -> Option<String> {
    for prefix in &[
        "/opt/homebrew/opt/llvm@18/bin",
        "/opt/homebrew/opt/llvm/bin",
        "/usr/local/opt/llvm@18/bin",
        "/usr/local/opt/llvm/bin",
    ] {
        let path = format!("{}/llvm-objcopy", prefix);
        if std::path::Path::new(&path).exists() {
            return Some(path);
        }
    }
    if std::process::Command::new("llvm-objcopy")
        .arg("--version")
        .output()
        .is_ok()
    {
        return Some("llvm-objcopy".to_string());
    }
    if std::process::Command::new("objcopy").arg("--version").output().is_ok() {
        return Some("objcopy".to_string());
    }
    None
}

/// Strip LLVM static constructors from a static archive to prevent segfaults (LIM-010).
///
/// Uses `llvm-objcopy` directly on the archive file to remove constructor/destructor
/// sections from every member, preserving duplicate-named members (e.g. multiple
/// `Error.cpp.o`) that `ar x` would silently overwrite.
pub(crate) fn strip_llvm_constructors(lib: &Path, temp_dir: &Path) -> Result<PathBuf, String> {
    let objcopy = find_objcopy_tool();
    let objcopy = match objcopy {
        Some(cmd) => cmd,
        None => return Ok(lib.to_path_buf()),
    };

    let archive_path = safe_canonicalize(lib);
    let filtered = temp_dir.join("libsimple_native_all_stripped.a");

    let mut cmd = std::process::Command::new(&objcopy);
    cmd.arg("--remove-section=.init_array")
        .arg("--remove-section=.ctors")
        .arg("--remove-section=.fini_array")
        .arg("--remove-section=.dtors");
    // NOTE(2026-04-15): we deliberately do NOT strip __DATA,__mod_init_func /
    // __mod_term_func on macOS even though LIM-010 (LLVM static constructor
    // segfault) used to require it. ObjC class registration also lives in
    // __mod_init_func, and stripping it leaves NSApplication / NSWindow
    // un-registered, so the first AppKit method dispatch goes through the
    // forwarding path and crashes inside dyld with a NULL selector name (see
    // crash analysis in src/runtime/hosted/cocoa.rs comments). LIM-010 only
    // affects the LLVM backend, which is opt-in via `--backend=llvm-lib`.
    cmd.arg(&archive_path).arg(&filtered);

    let status = cmd.status().map_err(|e| format!("llvm-objcopy on archive: {e}"))?;
    if !status.success() {
        return Ok(lib.to_path_buf());
    }
    Ok(filtered)
}

/// Check if a mangled symbol name refers to a C standard library / system function.
#[cfg(any(
    target_os = "macos",
    target_os = "freebsd",
    target_os = "linux",
    target_os = "windows"
))]
pub(crate) fn is_system_symbol(sym: &str) -> bool {
    #[cfg(target_os = "windows")]
    {
        let name = sym.strip_prefix('_').unwrap_or(sym);
        return is_windows_system_name(sym) || is_windows_system_name(name);
    }
    let name = sym.strip_prefix('_').unwrap_or(sym);
    if is_known_system_name(sym) || is_known_system_name(name) {
        return true;
    }
    if cfg!(target_os = "macos") {
        return is_macos_system_symbol(sym);
    }
    #[cfg(target_os = "windows")]
    if is_windows_system_name(sym) || is_windows_system_name(name) {
        return true;
    }
    false
}

/// Return true for libgcc/compiler-rt low-level helper names.
///
/// Freestanding links must resolve these from compiler-rt/libgcc, not from the
/// weak unresolved-symbol stubs. Stubbing these would make RV32 soft-float
/// programs link while producing incorrect arithmetic at runtime.
pub(crate) fn is_compiler_rt_builtin_symbol(sym: &str) -> bool {
    let name = sym.strip_prefix('_').unwrap_or(sym);
    if !sym.starts_with("__") && !name.starts_with("__") {
        return false;
    }
    let builtin_prefixes = [
        "__add",
        "__sub",
        "__mul",
        "__div",
        "__mod",
        "__udiv",
        "__umod",
        "__udivmod",
        "__ashl",
        "__ashr",
        "__lshr",
        "__cmp",
        "__ucmp",
        "__neg",
        "__clz",
        "__ctz",
        "__popcount",
        "__parity",
        "__bswap",
        "__fix",
        "__fixuns",
        "__float",
        "__floatun",
        "__extend",
        "__trunc",
        "__eq",
        "__ne",
        "__lt",
        "__le",
        "__gt",
        "__ge",
        "__unord",
        "__powi",
        "__multi3",
    ];
    builtin_prefixes
        .iter()
        .any(|prefix| sym.starts_with(prefix) || name.starts_with(prefix))
}

#[cfg(target_os = "windows")]
fn is_windows_system_name(name: &str) -> bool {
    matches!(
        name,
        "malloc"
            | "calloc"
            | "realloc"
            | "free"
            | "aligned_alloc"
            | "memcpy"
            | "memmove"
            | "memset"
            | "memcmp"
            | "memchr"
            | "strlen"
            | "strcmp"
            | "strncmp"
            | "strcpy"
            | "strncpy"
            | "strcat"
            | "strdup"
            | "strerror"
            | "strstr"
            | "strchr"
            | "strrchr"
            | "strtol"
            | "strtoul"
            | "strtod"
            | "printf"
            | "fprintf"
            | "sprintf"
            | "snprintf"
            | "puts"
            | "fputs"
            | "fputc"
            | "fwrite"
            | "fread"
            | "fopen"
            | "fclose"
            | "fflush"
            | "fseek"
            | "ftell"
            | "exit"
            | "_exit"
            | "abort"
            | "atexit"
            | "getenv"
            | "system"
            | "sqrt"
            | "sqrtf"
            | "sin"
            | "cos"
            | "tan"
            | "exp"
            | "log"
            | "pow"
            | "fabs"
            | "ceil"
            | "floor"
            | "round"
            | "fmod"
            | "qsort"
            | "bsearch"
            | "abs"
            | "labs"
            | "rand"
            | "srand"
            | "isdigit"
            | "isalpha"
            | "isspace"
            | "tolower"
            | "toupper"
            | "setlocale"
            | "time"
            | "clock"
            | "__security_cookie"
            | "__security_check_cookie"
            | "__GSHandlerCheck"
            | "__acrt_iob_func"
            | "__stdio_common_vfprintf"
            | "__stdio_common_vsprintf"
    )
}

fn is_macos_system_symbol(sym: &str) -> bool {
    let name = sym.strip_prefix('_').unwrap_or(sym);

    if matches!(
        name,
        "__stderrp" | "__stdinp" | "__stdoutp" | "_stderrp" | "_stdinp" | "_stdoutp"
    ) {
        return true;
    }

    if name.starts_with("_Z")
        || name.starts_with("__Z")
        || name.starts_with("_ZN")
        || name.starts_with("_ZT")
        || name.starts_with("_ZS")
        || name.starts_with("__cxa_")
        || name.starts_with("__cxx")
    {
        return true;
    }

    if name.starts_with("objc_") || name.starts_with("_objc_") || name.starts_with("OBJC_") {
        return true;
    }

    if name.starts_with("CF")
        || name.starts_with("kCF")
        || name.starts_with("CC")
        || name.starts_with("Sec")
        || name.starts_with("kSec")
        || name.starts_with("IORegistr")
        || name.starts_with("IOService")
        || name.starts_with("IOObject")
        || name.starts_with("SCDynamic")
        || name.starts_with("SCNetwork")
        || name.starts_with("kSC")
        || name.starts_with("NSApp")
        || name.starts_with("NSView")
        || name.starts_with("NSWindow")
        || name.starts_with("NSFile")
        || name.starts_with("NSKey")
        || name.starts_with("NSConcrete")
        || name.starts_with("_NSGet")
        || name.starts_with("_NSConcrete")
        || name.starts_with("dispatch_")
        || name.starts_with("_dispatch_")
        || name.starts_with("xpc_")
        || name.starts_with("notify_")
        || name.starts_with("os_log")
        || name.starts_with("Block_")
        || name.starts_with("_Block_")
    {
        return true;
    }

    if matches!(
        name,
        "arc4random"
            | "arc4random_buf"
            | "arc4random_uniform"
            | "__error"
            | "__maskrune"
            | "__tolower"
            | "__toupper"
            | "_NSGetExecutablePath"
            | "_NSGetEnviron"
            | "_NSGetArgc"
            | "_NSGetArgv"
            | "__NSConcreteStackBlock"
            | "__NSConcreteGlobalBlock"
            | "os_unfair_lock_lock"
            | "os_unfair_lock_unlock"
            | "mach_absolute_time"
            | "mach_timebase_info"
            | "mach_task_self_"
            | "vm_allocate"
            | "vm_deallocate"
            | "kevent"
            | "kqueue"
            | "pipe2"
            | "flock"
            | "ftruncate"
            | "pread"
            | "pwrite"
            | "writev"
            | "readv"
            | "getifaddrs"
            | "freeifaddrs"
            | "if_nametoindex"
            | "sysctl"
            | "sysctlbyname"
            | "proc_pidpath"
            | "issetugid"
            | "sandbox_check"
    ) {
        return true;
    }

    if name.starts_with("pthread_") || name.starts_with("dispatch_") || name.starts_with("mach_") {
        return true;
    }

    false
}

fn is_known_system_name(name: &str) -> bool {
    if name.starts_with("_Z") || name.starts_with("__Z") {
        return true;
    }
    matches!(
        name,
        "malloc"
            | "calloc"
            | "realloc"
            | "free"
            | "posix_memalign"
            | "aligned_alloc"
            | "memcpy"
            | "memmove"
            | "memset"
            | "memcmp"
            | "memchr"
            | "strlen"
            | "strcmp"
            | "strncmp"
            | "strcpy"
            | "strncpy"
            | "strcat"
            | "strdup"
            | "strerror"
            | "strstr"
            | "strchr"
            | "strrchr"
            | "strtol"
            | "strtoul"
            | "strtod"
            | "strtoll"
            | "strtoull"
            | "printf"
            | "fprintf"
            | "sprintf"
            | "snprintf"
            | "puts"
            | "fputs"
            | "fputc"
            | "fwrite"
            | "fread"
            | "fopen"
            | "fclose"
            | "fflush"
            | "fseek"
            | "ftell"
            | "feof"
            | "ferror"
            | "fileno"
            | "fdopen"
            | "freopen"
            | "getline"
            | "getdelim"
            | "stdin"
            | "stdout"
            | "stderr"
            | "sqrt"
            | "sqrtf"
            | "sin"
            | "cos"
            | "tan"
            | "asin"
            | "acos"
            | "atan"
            | "atan2"
            | "exp"
            | "expf"
            | "log"
            | "logf"
            | "log2"
            | "log10"
            | "pow"
            | "powf"
            | "fabs"
            | "fabsf"
            | "ceil"
            | "ceilf"
            | "floor"
            | "floorf"
            | "round"
            | "roundf"
            | "fmod"
            | "fmodf"
            | "fmin"
            | "fmax"
            | "copysign"
            | "nan"
            | "isnan"
            | "isinf"
            | "trunc"
            | "truncf"
            | "exit"
            | "_exit"
            | "abort"
            | "atexit"
            | "getenv"
            | "setenv"
            | "unsetenv"
            | "system"
            | "fork"
            | "execve"
            | "execvp"
            | "waitpid"
            | "kill"
            | "getpid"
            | "getppid"
            | "signal"
            | "sigaction"
            | "sigemptyset"
            | "sigfillset"
            | "sigaddset"
            | "pthread_create"
            | "pthread_join"
            | "pthread_detach"
            | "pthread_self"
            | "pthread_mutex_init"
            | "pthread_mutex_lock"
            | "pthread_mutex_unlock"
            | "pthread_mutex_destroy"
            | "pthread_rwlock_init"
            | "pthread_rwlock_destroy"
            | "pthread_rwlock_rdlock"
            | "pthread_rwlock_wrlock"
            | "pthread_rwlock_unlock"
            | "pthread_cond_init"
            | "pthread_cond_wait"
            | "pthread_cond_signal"
            | "pthread_cond_broadcast"
            | "pthread_cond_destroy"
            | "dlopen"
            | "dlclose"
            | "dlsym"
            | "dlerror"
            | "open"
            | "close"
            | "read"
            | "write"
            | "lseek"
            | "stat"
            | "fstat"
            | "lstat"
            | "mkdir"
            | "rmdir"
            | "unlink"
            | "rename"
            | "getcwd"
            | "chdir"
            | "access"
            | "realpath"
            | "readlink"
            | "symlink"
            | "opendir"
            | "readdir"
            | "readdir_r"
            | "closedir"
            | "dirfd"
            | "fdopendir"
            | "scandir"
            | "getdirentries64"
            | "socket"
            | "bind"
            | "listen"
            | "accept"
            | "connect"
            | "send"
            | "recv"
            | "sendto"
            | "recvfrom"
            | "setsockopt"
            | "getsockopt"
            | "getaddrinfo"
            | "freeaddrinfo"
            | "inet_ntop"
            | "inet_pton"
            | "htons"
            | "ntohs"
            | "htonl"
            | "time"
            | "clock"
            | "clock_gettime"
            | "gettimeofday"
            | "nanosleep"
            | "usleep"
            | "sleep"
            | "qsort"
            | "bsearch"
            | "abs"
            | "labs"
            | "rand"
            | "srand"
            | "isdigit"
            | "isalpha"
            | "isspace"
            | "tolower"
            | "toupper"
            | "mmap"
            | "munmap"
            | "mprotect"
            | "sysconf"
            | "pipe"
            | "dup"
            | "dup2"
            | "fcntl"
            | "ioctl"
            | "select"
            | "poll"
            | "gnu_get_libc_version"
            | "confstr"
            | "getauxval"
            | "dl_iterate_phdr"
            | "__libc_start_main"
            | "__cxa_atexit"
            | "__cxa_finalize"
            | "__cxa_thread_atexit_impl"
            | "__errno_location"
            | "__stack_chk_fail"
            | "__stack_chk_guard"
            | "posix_spawn"
            | "posix_spawnattr_init"
            | "posix_spawnattr_setflags"
            | "posix_spawnattr_setsigdefault"
            | "posix_spawnattr_setsigmask"
            | "posix_spawnattr_setpgroup"
            | "posix_spawnattr_destroy"
            | "posix_spawn_file_actions_init"
            | "posix_spawn_file_actions_adddup2"
            | "posix_spawn_file_actions_addopen"
            | "posix_spawn_file_actions_addclose"
            | "posix_spawn_file_actions_destroy"
            | "posix_spawnp"
            | "setlocale"
            | "nl_langinfo"
            | "getpwuid_r"
            | "getuid"
            | "geteuid"
            | "prctl"
            | "sched_getaffinity"
            | "getrandom"
            | "syscall"
            | "epoll_create1"
            | "epoll_ctl"
            | "epoll_wait"
            | "eventfd"
            | "futex"
            | "madvise"
            | "mremap"
            | "mincore"
    )
}
