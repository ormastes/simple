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

## File Operations

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
 * @param size Bytes to read (-1 = read to end)
 * @return File content or NULL on error
 */
const char* rt_file_read_text_at(const char* path, int64_t offset, int64_t size);

/**
 * Write file content at specific offset.
 * @param path File path
 * @param offset Byte offset
 * @param data Content to write
 * @return true on success, false on failure
 */
bool rt_file_write_text_at(const char* path, int64_t offset, const char* data);

/**
 * Get file size.
 * @param path File path
 * @return Size in bytes, or -1 on error
 */
int64_t rt_file_size(const char* path);
```

## Memory-Mapped I/O

```c
/**
 * Memory-map a file for reading.
 * @param path File path
 * @param out_size Output parameter for file size
 * @return Mapped memory pointer, or NULL on failure
 */
void* rt_mmap_read(const char* path, int64_t* out_size);

/**
 * Memory-map a file for writing.
 * @param path File path
 * @param size File size (will be created/resized)
 * @return Mapped memory pointer, or NULL on failure
 */
void* rt_mmap_write(const char* path, int64_t size);

/**
 * Unmap memory-mapped file.
 * @param addr Address from rt_mmap_read/write
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
bool rt_madvise(void* addr, int64_t size, int advice);
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
| Windows | `platform_win.h` | (standalone) | ✅ Tier 2 |

## Implementation Notes

### Unix Platforms (Linux, macOS, FreeBSD)

All Unix platforms share `unix_common.h` (415 lines) which implements the full API using POSIX functions:
- Directory ops: `opendir()`, `readdir()`, `nftw()`
- File ops: `open()`, `flock()`, `pread()`, `pwrite()`
- Memory-mapped I/O: `mmap()`, `munmap()`, `msync()`, `madvise()`
- Process ops: `fork()`, `exec()`, `waitpid()`, `kill()`

Platform-specific headers only set feature macros:
- **Linux**: (none needed)
- **macOS**: `#define _DARWIN_C_SOURCE`
- **FreeBSD**: `#define __BSD_VISIBLE 1`

### Windows Platform

Windows implementation in `platform_win.h` (489 lines) uses Win32 API:
- Directory ops: `CreateDirectoryA()`, `FindFirstFileA()`, `RemoveDirectoryA()`
- File ops: `CreateFileA()`, `LockFileEx()`, `ReadFile()`, `WriteFile()`
- Memory-mapped I/O: `CreateFileMappingA()`, `MapViewOfFile()`, `FlushViewOfFile()`
- Process ops: `CreateProcessA()`, `WaitForSingleObject()`, `TerminateProcess()`

## Adding New Platform

To add support for a new platform:

1. Create `seed/platform/platform_newos.h`
2. Implement all functions listed above
3. Add platform detection to `seed/platform/platform.h`:
   ```c
   #elif defined(__NEWOS__)
   #  include "platform_newos.h"
   ```
4. Create startup CRT: `seed/startup/newos/crt_newos.c`
5. Test bootstrap: Build seed compiler and verify all functions work

## Verification

To verify platform conformance:

```bash
# Extract function signatures
grep "^[a-z_]*\s*rt_" seed/platform/unix_common.h | sed 's/ {$/;/'
grep "^[a-z_]*\s*rt_" seed/platform/platform_win.h | sed 's/ {$/;/'

# Should be identical
```

## Version History

- 2026-02-13: Initial API documentation (Phase 4 cleanup)
- Function count: 21 rt_* functions across 4 categories
