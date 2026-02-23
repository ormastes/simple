# Platform API Contract

All platform headers (`platform_*.h`) must implement this exact API contract.
The seed compiler is platform-independent; all platform differences are isolated to these headers.

## Directory Operations

```c
/**
 * Create a directory.
 * @param path Directory path
 * @param recursive If true, create parent directories as needed
 * @return true on success, false on failure
 */
bool rt_dir_create(const char* path, bool recursive);

/**
 * List directory contents.
 * @param path Directory path
 * @param out_count Output parameter for entry count
 * @return Array of entry names (null-terminated), or NULL on failure
 *         Caller must free with rt_dir_list_free()
 *         Excludes "." and ".." entries
 */
const char** rt_dir_list(const char* path, int64_t* out_count);

/**
 * Free directory listing.
 * @param entries Array returned by rt_dir_list()
 * @param count Entry count from rt_dir_list()
 */
void rt_dir_list_free(const char** entries, int64_t count);

/**
 * Recursively remove directory and all contents.
 * @param path Directory path
 * @return true on success, false on failure
 */
bool rt_dir_remove_all(const char* path);
```

## File Locking + Offset File I/O

```c
/**
 * Acquire exclusive file lock.
 * @param path File path (created if doesn't exist)
 * @param timeout_secs Timeout in seconds (0 = blocking, >0 = timeout)
 * @return File handle (>0) on success, -1 on failure/timeout
 */
int64_t rt_file_lock(const char* path, int64_t timeout_secs);

/**
 * Release file lock and close file.
 * @param handle File handle from rt_file_lock()
 * @return true on success, false on failure
 */
bool rt_file_unlock(int64_t handle);

/**
 * Read file content at specific offset.
 * @param path File path
 * @param offset Byte offset
 * @param size Bytes to read
 * @return Heap string on success, empty string on error
 */
const char* rt_file_read_text_at(const char* path, int64_t offset, int64_t size);

/**
 * Write file content at specific offset.
 * @param path File path
 * @param offset Byte offset
 * @param data Content to write
 * @return Bytes written, or -1 on failure
 */
int64_t rt_file_write_text_at(const char* path, int64_t offset, const char* data);
```

## Memory-Mapped I/O

```c
/**
 * Memory-map a file region.
 * @param path File path
 * @param size Mapping size
 * @param offset Mapping offset
 * @param readonly True for read-only mapping
 * @return Mapped memory pointer, or NULL on failure
 */
void* rt_mmap(const char* path, int64_t size, int64_t offset, bool readonly);

/**
 * Unmap memory-mapped file.
 * @param addr Address from rt_mmap()
 * @param size Mapped size
 * @return true on success, false on failure
 */
bool rt_munmap(void* addr, int64_t size);

/**
 * Flush memory-mapped changes to disk.
 * @param addr Mapped address
 * @param size Mapped size
 * @return true on success, false on failure
 */
bool rt_msync(void* addr, int64_t size);

/**
 * Advise kernel on memory usage pattern.
 * @param addr Mapped address
 * @param size Mapped size
 * @param advice Platform-specific advice constant
 * @return true on success, false on failure
 */
bool rt_madvise(void* addr, int64_t size, int64_t advice);
```

## High-Resolution Time

```c
int64_t rt_time_now_nanos(void);
int64_t rt_time_now_micros(void);
```

## Process Operations

```c
/**
 * Spawn process asynchronously.
 * @param cmd Command to execute
 * @param args Argument array (null-terminated)
 * @param arg_count Number of arguments
 * @return Process ID (>0) on success, -1 on failure
 */
int64_t rt_process_spawn_async(const char* cmd, const char** args, int64_t arg_count);

/**
 * Wait for process completion.
 * @param pid Process ID from rt_process_spawn_async()
 * @param timeout_ms Timeout in milliseconds (0 = wait forever)
 * @return Exit code on success, -1 on error, -2 on timeout
 */
int64_t rt_process_wait(int64_t pid, int64_t timeout_ms);

/**
 * Check if process is running.
 * @param pid Process ID
 * @return true if running, false otherwise
 */
bool rt_process_is_running(int64_t pid);

/**
 * Terminate process.
 * @param pid Process ID
 * @return true on success, false on failure
 */
bool rt_process_kill(int64_t pid);
```

## Platform Support Matrix

| Platform | Header | Shared Code | Status |
|----------|--------|-------------|--------|
| Linux | `platform_linux.h` | `unix_common.h` | ✅ Tier 1 |
| macOS | `platform_macos.h` | `unix_common.h` | ✅ Tier 1 |
| FreeBSD | `platform_freebsd.h` | `unix_common.h` | ✅ Tier 1 |
| OpenBSD | `platform_openbsd.h` | `unix_common.h` | ⚠️ Tier 2 (shared path) |
| NetBSD | `platform_netbsd.h` | `unix_common.h` | ⚠️ Tier 2 (shared path) |
| Windows | `platform_win.h` | (standalone) | ✅ Tier 2 |

## Implementation Notes

### Unix Platforms (Linux, macOS, FreeBSD, OpenBSD, NetBSD)

All Unix platforms share `unix_common.h` which implements the full API using POSIX functions:
- Directory ops: `opendir()`, `readdir()`, `nftw()`
- File ops: `open()`, `flock()`, `pread()`, `pwrite()`
- Memory-mapped I/O: `mmap()`, `munmap()`, `msync()`, `madvise()`
- Process ops: `fork()`, `exec()`, `waitpid()`, `kill()`

Platform-specific headers are thin selectors over the shared implementation:
- **Linux**: (none needed)
- **macOS**: `#define _DARWIN_C_SOURCE`
- **FreeBSD**: `#define __BSD_VISIBLE 1`
- **OpenBSD**: `platform_openbsd.h` includes `unix_common.h`
- **NetBSD**: `platform_netbsd.h` includes `unix_common.h`

### Windows Platform

Windows implementation in `platform_win.h` uses Win32 API:
- Directory ops: `CreateDirectoryA()`, `FindFirstFileA()`, `RemoveDirectoryA()`
- File ops: `CreateFileA()`, `LockFileEx()`, `ReadFile()`, `WriteFile()`
- Memory-mapped I/O: `CreateFileMappingA()`, `MapViewOfFile()`, `FlushViewOfFile()`
- Process ops: `CreateProcessA()`, `WaitForSingleObject()`, `TerminateProcess()`

## Adding New Platform

To add support for a new platform:

1. Create `src/compiler_src/compiler_seed/platform/platform_newos.h`
2. Implement all functions listed above
3. Add platform detection to `src/compiler_src/compiler_seed/platform/platform.h`:
   ```c
   #elif defined(__NEWOS__)
   #  include "platform_newos.h"
   ```
4. Create startup CRT: `src/compiler_seed/startup/newos/crt_newos.c`
5. Test bootstrap: Build seed compiler and verify all functions work

## Verification

To verify platform conformance:

```bash
# Extract function signatures
awk '/^(bool|int64_t|const char\\*\\*|const char\\*|void\\*|void) rt_[a-z0-9_]+\\(/ {print $0}' src/compiler_src/compiler_seed/platform/unix_common.h
awk '/^(bool|int64_t|const char\\*\\*|const char\\*|void\\*|void) rt_[a-z0-9_]+\\(/ {print $0}' src/compiler_src/compiler_seed/platform/platform_win.h

# Should be identical
```

## Cross-Platform System Functions (added 2026-02-19)

The following functions are implemented in each platform header (unix_common.h and platform_win.h) and declared in runtime.h:

```c
/** Get current working directory. Returns heap string, caller owns it. */
char* rt_getcwd(void);

/** Check if path is a directory. */
bool rt_is_dir(const char* path);

/** Rename/move a file. On Windows uses MoveFileA (fails if dst exists). */
bool rt_rename(const char* src, const char* dst);

/** Sleep for ms milliseconds. Named _native to avoid Simple name collision. */
void rt_sleep_ms_native(int64_t ms);

/** Get current process ID. */
int64_t rt_getpid(void);

/** Get hostname. Returns heap string, caller owns it. */
char* rt_hostname(void);

/** Get logical CPU count for parallelism. */
int64_t rt_thread_available_parallelism(void);

/** Get Unix epoch time in microseconds. */
int64_t rt_time_now_unix_micros(void);

/** Set environment variable. Returns true on success. */
bool rt_env_set(const char* key, const char* value);
```

## `rt_` Functions in runtime.c (not platform headers)

These functions return `SplArray*` so must be in runtime.c (after SplArray is defined):

```c
/** Recursively walk directory, returning all file paths. */
SplArray* rt_dir_walk(const char* path);

/** List immediate directory contents as SplArray of strings. */
SplArray* rt_dir_list_array(const char* path);

/** Append content to file. Returns 1 on success. */
int rt_file_append(const char* path, const char* content);

/** Write content to file. Returns 1 on success (was void, now int). */
int rt_file_write(const char* path, const char* content);
```

## Version History

- 2026-02-13: Initial API documentation (Phase 4 cleanup)
- 2026-02-19: Synced signatures with runtime/platform headers and split OpenBSD/NetBSD selectors
- 2026-02-19: Added 9 new cross-platform functions (getcwd, is_dir, rename, sleep_ms_native, getpid, hostname, thread_available_parallelism, time_now_unix_micros, env_set) + 4 runtime.c functions (dir_walk, dir_list_array, file_append, fixed file_write return type)
- Function count: 27 rt_* functions total
