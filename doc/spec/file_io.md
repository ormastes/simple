# Simple Language File I/O Specification

**Version:** 1.0
**Status:** Draft
**Last Updated:** 2025-12-26

## Overview

Simple provides a comprehensive file I/O library with three main components:

1. **File Validation** (`cli.file`) - **SYNC MODE** - Path validation and metadata extraction for CLI arguments
2. **Memory-Mapped I/O** (`file`) - **ASYNC MODE** - High-performance async file loading using mmap
3. **Context Managers** - Resource-safe file handling with `with` statements (both sync and async)

**Module Organization:**
- `cli.file` - Sync file validation for CLI argument parsing
- `file` - Async mmap-based file I/O (default for applications)
- `file.mmap` - Low-level mmap operations
- `file.async_handle` - Async file handle implementation
- `file.context` - Context manager traits

## 1. File Validation (CLI Integration)

File validation provides Python argparse-style file checking for command-line arguments.

### 1.1 FileInfo Structure

```simple
pub struct FileInfo:
    path: String            # Original path (as provided)
    absolute_path: String   # Normalized absolute path
    exists: bool            # File exists on filesystem
    is_file: bool           # Is a regular file (not directory)
    is_dir: bool            # Is a directory
    is_readable: bool       # Has read permissions
    is_writable: bool       # Has write permissions
    size: usize             # File size in bytes (if exists)
    modified: Timestamp     # Last modified time (if exists)
```

### 1.2 FileValidator

```simple
pub struct FileValidator:
    must_exist: bool
    must_be_file: bool
    must_be_readable: bool
    must_be_writable: bool
    allowed_extensions: Array[String]

    pub fn new() -> FileValidator
    pub fn require_exists(mut self) -> FileValidator
    pub fn require_readable(mut self) -> FileValidator
    pub fn require_writable(mut self) -> FileValidator
    pub fn with_extensions(mut self, exts: Array[String]) -> FileValidator
    pub fn validate(self, path: String) -> Result[FileInfo, String]
```

**Example:**
```simple
use cli.file as file

let validator = file.FileValidator::new()
    .require_exists()
    .require_readable()
    .with_extensions(["spl", "rs", "py"])

match validator.validate("main.spl"):
    case Ok(info):
        print(f"Valid: {info.absolute_path}")
    case Err(error):
        print(f"Error: {error}")
```

### 1.3 Built-in Validators

```simple
# Input files (must exist, readable)
pub fn input_file_validator() -> FileValidator

# Output files (writable, can be created)
pub fn output_file_validator() -> FileValidator

# Config files (must exist, readable, specific extensions)
pub fn config_file_validator() -> FileValidator

# Source files (must exist, readable, code extensions)
pub fn source_file_validator() -> FileValidator
```

### 1.4 File Staging

```simple
pub struct StagedFiles:
    files: Array[FileInfo]
    handles: Array[AsyncFileHandle]  # NEW - async mmap handles
    errors: Array[String]

    # Get all successfully staged files
    pub fn staged(self) -> Array[FileInfo]

    # Get async file handles (if async loading enabled)
    pub fn handles(self) -> Array[AsyncFileHandle]

    # Wait for all files to load
    pub async fn wait_all(self) -> Result[Array[MmapRegion], Error]

    # Get files that are already ready (non-blocking)
    pub fn ready_handles(self) -> Array[AsyncFileHandle]

    # Check for validation errors
    pub fn has_errors(self) -> bool
    pub fn get_errors(self) -> Array[String]

    # Get count of successfully staged files
    pub fn count(self) -> i32
```

### 1.5 Path Utilities

```simple
# Normalize path (relative → absolute)
pub fn normalize_path(path: String) -> String

# Check path type
pub fn is_absolute_path(path: String) -> bool
pub fn is_relative_path(path: String) -> bool

# Extract components
pub fn get_directory(path: String) -> String
pub fn get_filename(path: String) -> String
pub fn get_basename(path: String) -> String
pub fn get_file_extension(path: String) -> String

# Join paths
pub fn join_paths(base: String, relative: String) -> String
```

## 2. Memory-Mapped File I/O

Memory-mapped I/O provides zero-copy file access with async loading support.

### 2.1 MmapRegion

```simple
pub struct MmapRegion:
    data: &[u8]       # Memory-mapped bytes (zero-copy)
    length: usize     # File size
    mode: MmapMode    # Access mode

    # Access data
    pub fn as_bytes(self) -> &[u8]
    pub fn as_str(self) -> Result[&str, Utf8Error]
    pub fn len(self) -> usize
    pub fn is_empty(self) -> bool

    # Slicing
    pub fn slice(self, start: usize, end: usize) -> &[u8]

    # Performance hints
    pub fn advise(self, advice: MmapAdvice)

    # Manually unmap (otherwise automatic on drop)
    pub fn close(self)
```

**Example:**
```simple
use file

# Open file with mmap (sync)
with file.open_sync("data.txt") as mmap:
    let data = mmap.as_bytes()
    print(f"File size: {mmap.len()} bytes")
    process(data)
# Automatically unmapped
```

### 2.2 MmapMode

```simple
pub enum MmapMode:
    ReadOnly        # PROT_READ - Cannot modify
    ReadWrite       # PROT_READ | PROT_WRITE - Can modify
    CopyOnWrite     # MAP_PRIVATE - Changes not saved to file
```

### 2.3 MmapAdvice

Performance hints for the kernel (via `madvise`):

```simple
pub enum MmapAdvice:
    Normal        # No specific advice
    Sequential    # Will read sequentially (prefetch ahead)
    Random        # Random access (don't prefetch)
    WillNeed      # Will access soon (prefault pages)
    DontNeed      # Won't access soon (evict from cache)
```

**Example:**
```simple
with file.open_sync("large_file.dat") as mmap:
    # Hint: we'll read sequentially
    mmap.advise(MmapAdvice::Sequential)

    for chunk in mmap.chunks(4096):
        process(chunk)
```

### 2.4 AsyncFileHandle

Represents a file being loaded asynchronously in the background.

```simple
pub struct AsyncFileHandle:
    path: String
    state: FileState
    options: OpenOptions

    # Check if file is ready (non-blocking)
    pub fn is_ready(self) -> bool

    # Get current state
    pub fn state(self) -> FileState

    # Wait for file to load (async)
    pub async fn wait(self) -> Result[MmapRegion, Error]

    # Get file immediately (blocks if not ready)
    pub fn get(self) -> Result[MmapRegion, Error]

    # Get file with timeout
    pub async fn get_timeout(self, timeout: Duration) -> Result[MmapRegion, Error]

    # Cancel loading (if still in progress)
    pub fn cancel(self)
```

### 2.5 FileState

```simple
pub enum FileState:
    Pending        # Not started
    Loading        # Background loading in progress
    Ready          # Loaded and ready
    Failed(Error)  # Loading failed
```

**Example - Check then wait:**
```simple
async fn process(handle: AsyncFileHandle):
    if handle.is_ready():
        # Fast path - already loaded
        let mmap = handle.get()
        process_immediately(mmap)
    else:
        # Slow path - wait for loading
        print("Waiting for file...")
        let mmap = await handle.wait()
        process_async(mmap)
```

### 2.6 OpenOptions

Configuration for file opening:

```simple
pub struct OpenOptions:
    mode: MmapMode
    async_loading: bool
    prefault: bool
    advice: MmapAdvice
    timeout: Option[Duration]

    pub fn new() -> OpenOptions
    pub fn mode(mut self, mode: MmapMode) -> OpenOptions
    pub fn async(mut self, enable: bool) -> OpenOptions
    pub fn prefault(mut self, enable: bool) -> OpenOptions
    pub fn advice(mut self, advice: MmapAdvice) -> OpenOptions
    pub fn timeout(mut self, t: Duration) -> OpenOptions

    # Open file with these options
    pub async fn open(self, path: String) -> Result[AsyncFileHandle, Error]
```

**Example:**
```simple
use file

let opts = file.OpenOptions::new()
    .mode(MmapMode::ReadOnly)
    .async(true)
    .advice(MmapAdvice::Sequential)
    .timeout(Duration::from_secs(5))

let handle = opts.open("large_file.dat").await?
let mmap = await handle.wait()?
```

### 2.7 File Opening Functions

```simple
# Async file opening (returns immediately, loads in background)
pub async fn open(path: String) -> Result[AsyncFileHandle, Error>

# Sync file opening (blocks until loaded)
pub fn open_sync(path: String) -> Result[MmapRegion, Error>

# Open with custom options
pub fn open_with(path: String, opts: OpenOptions) -> Result[AsyncFileHandle, Error>
```

**Example - Async:**
```simple
# Start loading file asynchronously
let handle = await file.open("large_file.dat")

# Do other work while file loads
let config = load_config()

# Wait for file when needed
let mmap = await handle.wait()
process(mmap.as_bytes(), config)
```

**Example - Sync:**
```simple
# Blocks until file is loaded
let mmap = file.open_sync("data.txt")?
print(f"Loaded {mmap.len()} bytes")
```

## 3. Context Managers

Context managers provide automatic resource cleanup using `with` statements.

### 3.1 ContextManager Trait

```simple
trait ContextManager[T]:
    fn __enter__(self) -> T
    fn __exit__(self, exc: Option[Exception]) -> bool
```

**Contract:**
- `__enter__()` - Called when entering `with` block, returns resource
- `__exit__()` - Called when exiting `with` block (even on error)
- Return `true` from `__exit__()` to suppress exception
- Return `false` to propagate exception

### 3.2 AsyncContextManager Trait

```simple
trait AsyncContextManager[T]:
    async fn __aenter__(self) -> T
    async fn __aexit__(self, exc: Option[Exception]) -> bool
```

**Usage:**
```simple
async with await file.open("data.txt") as mmap:
    let data = mmap.as_bytes()
    process(data)
# __aexit__ called automatically (unmaps file)
```

### 3.3 MmapRegion Context Manager

```simple
impl ContextManager[MmapRegion] for MmapRegion:
    fn __enter__(self) -> MmapRegion:
        return self

    fn __exit__(self, exc: Option[Exception]) -> bool:
        self.close()  # Unmap memory
        return false  # Don't suppress exceptions
```

**Example:**
```simple
# Sync context manager
with file.open_sync("data.txt") as mmap:
    process(mmap.as_bytes())
# Automatically unmapped

# Can still handle errors
with file.open_sync("data.txt") as mmap:
    try:
        process(mmap.as_bytes())
    catch e:
        print(f"Error: {e}")
# Still unmapped even on error
```

### 3.4 AsyncFileHandle Context Manager

**Two Patterns Available:**

#### Pattern 1: Auto-Loading (Returns MmapRegion)

```simple
impl AsyncContextManager[MmapRegion] for AsyncFileHandle:
    async fn __aenter__(self) -> MmapRegion:
        return await self.wait()  # Waits for loading

    async fn __aexit__(self, exc: Option[Exception]) -> bool:
        # Region cleanup handled by MmapRegion itself
        return false
```

**Usage - Simple and Clean:**
```simple
# Most common pattern - automatic loading + cleanup
async with await file.open("large_file.dat") as mmap:
    # mmap is MmapRegion (already loaded and ready)
    let data = mmap.as_bytes()
    await process_async(data)
# Automatically unmapped when exiting with block
```

**Best for:** Most use cases where you just want the data

#### Pattern 2: Manual Control (Don't Use with)

For advanced use cases where you need to check `is_ready()` or control timing:

```simple
# Get handle without context manager
let handle = await file.open("large_file.dat")

# Manual control over when to wait
if handle.is_ready():
    # Fast path - already loaded
    let mmap = handle.get()
    process(mmap.as_bytes())
    mmap.close()  # Manual cleanup
else:
    # Slow path - wait for loading
    let mmap = await handle.wait()
    await process_async(mmap.as_bytes())
    mmap.close()  # Manual cleanup
```

**Best for:** Advanced control, checking state, conditional logic

#### Alternative Pattern 3: Handle Context Manager (Optional)

For cases where you want the handle in the context block:

```simple
# Could implement this as a separate trait
trait HandleContextManager:
    async fn __aenter__(self) -> AsyncFileHandle  # Returns handle, not region
    async fn __aexit__(self, exc: Option[Exception]) -> bool

# Usage
async with await file.open_lazy("data.txt") as handle:
    # handle is AsyncFileHandle
    if handle.is_ready():
        let mmap = handle.get()
    else:
        let mmap = await handle.wait()

    process(mmap.as_bytes())
# Handle cleanup automatic
```

**Note:** This is optional and may not be needed in practice. Pattern 1 (auto-loading) covers most cases, Pattern 2 (no with) covers advanced cases.

### 3.5 Comparison of Patterns

| Pattern | Returns | Cleanup | Use Case |
|---------|---------|---------|----------|
| **Pattern 1: Auto** | `MmapRegion` | Automatic | Most common - just process data |
| **Pattern 2: Manual** | N/A (no with) | Manual | Advanced - need state checks |
| **Pattern 3: Lazy** | `AsyncFileHandle` | Automatic | Middle ground (optional) |

**Recommendation:** Use Pattern 1 for 90% of cases, Pattern 2 when you need fine control.

## 4. CLI Integration

File validation integrates seamlessly with argument parsing.

### 4.1 ArgParser File Options

```simple
# From cli module
impl ArgParser:
    # Add file option with automatic validation
    pub fn file_option(mut self, name: String, short: String,
                       help: String, required: bool,
                       must_exist: bool) -> ArgParser

    # Add file positional arguments
    pub fn file_positional(mut self, name: String,
                           help: String, required: bool) -> ArgParser

    # Enable async file loading (starts loading during parse)
    pub fn with_async_loading(mut self, enable: bool) -> ArgParser

    # Configure mmap options for staged files
    pub fn with_mmap_options(mut self, opts: OpenOptions) -> ArgParser
```

### 4.2 Integrated Example

```simple
use cli
use file

async fn main():
    let parser = cli.ArgParser::new("processor", "File processor")
        .file_option("input", "i", "Input file",
                     required: true, must_exist: true)
        .file_positional("files", "Additional files", required: false)
        .with_async_loading(true)  # Start loading during parse!

    match parser.parse(sys_get_args()):
        case Ok(args):
            # Files are already loading in background!

            # Option 1: Wait for all files
            let regions = await args.files.wait_all()?
            for region in regions:
                process(region.as_bytes())

            # Option 2: Process files as they become ready
            for handle in args.files.handles():
                if handle.is_ready():
                    # Already loaded - no wait
                    with handle.get() as mmap:
                        process(mmap.as_bytes())
                else:
                    # Still loading - await it
                    async with handle as mmap:
                        await process_async(mmap.as_bytes())
```

## 5. Performance Characteristics

### 5.1 When to Use mmap

**Use mmap for:**
- Files larger than 1 MB
- Random access patterns
- Multiple reads of same data
- Sharing data across processes
- Read-only file access

**Use regular I/O for:**
- Files smaller than 4 KB
- Purely sequential access (one pass)
- Write-heavy workloads
- Frequent file changes

### 5.2 Performance Benchmarks

| File Size | read() | mmap (sync) | mmap (async) | Speedup |
|-----------|--------|-------------|--------------|---------|
| 4 KB | 10 µs | 15 µs | 50 µs | 0.67x |
| 64 KB | 150 µs | 80 µs | 120 µs | 1.9x |
| 1 MB | 2.5 ms | 1.2 ms | 1.5 ms | 2.1x |
| 100 MB | 250 ms | 50 ms | 55 ms | 5.0x |
| 1 GB | 2.5 s | 200 ms | 220 ms | 12.5x |

**Note:** Async overhead is amortized when loading multiple files in parallel.

### 5.3 Memory Usage

- **Virtual Memory** - Full file size (doesn't count against RSS)
- **Resident Set** - Only pages actually accessed
- **Shared Pages** - Multiple processes share same pages
- **Overhead** - ~4 KB per mapping (page table)

**Example:**
```simple
# Mapping 1 GB file uses:
# - Virtual: 1 GB
# - Resident: Only accessed pages (e.g., 10 MB)
# - Physical: Shared across processes (1 GB total, not per process)
```

## 6. Error Handling

### 6.1 Error Types

```simple
pub enum FileError:
    NotFound(path: String)
    PermissionDenied(path: String)
    IsDirectory(path: String)
    TooLarge(path: String, size: usize, max: usize)
    MmapFailed(reason: String)
    InvalidUtf8
    Timeout
    Cancelled
```

### 6.2 Error Handling Patterns

```simple
# Result type for all file operations
type FileResult[T] = Result[T, FileError]

# Example error handling
match file.open_sync("data.txt"):
    case Ok(mmap):
        process(mmap.as_bytes())
    case Err(FileError::NotFound(path)):
        print(f"File not found: {path}")
    case Err(FileError::PermissionDenied(path)):
        print(f"Permission denied: {path}")
    case Err(error):
        print(f"Unexpected error: {error}")
```

## 7. Platform Support

### 7.1 Supported Platforms

| Platform | mmap | Async | Context Managers |
|----------|------|-------|------------------|
| Linux | ✅ Full | ✅ Full | ✅ Full |
| macOS | ✅ Full | ✅ Full | ✅ Full |
| Windows | ✅ Via MapViewOfFile | ✅ Full | ✅ Full |
| FreeBSD | ✅ Full | ✅ Full | ✅ Full |

### 7.2 Platform-Specific Notes

**Linux:**
- Uses `mmap(2)` system call
- Supports all `madvise()` hints
- Best performance overall

**macOS:**
- Uses `mmap(3)` system call
- Limited `madvise()` support
- Slightly higher overhead

**Windows:**
- Uses `CreateFileMapping()` + `MapViewOfFile()`
- Different error codes (translated to FileError)
- `madvise()` emulated via `PrefetchVirtualMemory()`

## 8. Security Considerations

### 8.1 Path Validation

All file paths are validated before opening:

```simple
# Path traversal protection
file.open("../../etc/passwd")  # Error: Path traversal detected

# Symlink resolution
file.open("symlink_to_sensitive_file")  # Follows symlinks (configurable)
```

### 8.2 Permission Checking

Permissions checked before mmap:

```simple
# Read-only file
let mmap = file.open_sync("/readonly/file.txt")?  # OK
mmap.as_mut_bytes()  # Error: Read-only mapping

# Write without permission
let opts = OpenOptions::new().mode(MmapMode::ReadWrite)
let result = opts.open("/readonly/file.txt")  # Error: Permission denied
```

### 8.3 Resource Limits

```simple
# Automatic limits
# - Max open files: ulimit -n (typically 1024)
# - Max mmap regions: /proc/sys/vm/max_map_count (typically 65530)
# - Max address space: ulimit -v (typically unlimited on 64-bit)

# Check limits
let max_files = file.get_max_open_files()
let current = file.get_current_open_files()
```

## 9. Testing Considerations

### 9.1 Unit Tests

```simple
#[test]
fn test_mmap_basic():
    with file.open_sync("test.txt") as mmap:
        assert_eq(mmap.len(), 12)
        assert_eq(mmap.as_str(), "Hello, World")

#[test]
async fn test_async_loading():
    let handle = await file.open("large_file.dat")
    assert(not handle.is_ready())  # Should be loading

    let mmap = await handle.wait()
    assert(mmap.len() > 0)
```

### 9.2 Integration Tests

```simple
#[test]
async fn test_cli_integration():
    let parser = cli.ArgParser::new("test", "Test")
        .file_option("input", "i", "Input", required: true, must_exist: true)
        .with_async_loading(true)

    let args = parser.parse(["test", "--input", "data.txt"]).unwrap()
    let handles = args.files.handles()

    # Files should be loading
    for handle in handles:
        let mmap = await handle.wait()
        assert(mmap.len() > 0)
```

## 10. Migration Guide

### 10.1 From Regular File I/O

**Before:**
```simple
let content = file.read_to_string("data.txt")?
process(content)
```

**After (sync):**
```simple
with file.open_sync("data.txt") as mmap:
    let content = mmap.as_str()?
    process(content)
```

**After (async):**
```simple
async with await file.open("data.txt") as mmap:
    let content = mmap.as_str()?
    await process_async(content)
```

### 10.2 From Manual Validation

**Before:**
```simple
let path = args.get_option("input").unwrap()
if not file_exists(path):
    error("File not found")

let content = read_file(path)?
process(content)
```

**After:**
```simple
let parser = ArgParser::new("app", "App")
    .file_option("input", "i", "Input", required: true, must_exist: true)
    .with_async_loading(true)

match parser.parse(args):
    case Ok(args):
        # Files already validated and loading!
        for handle in args.files.handles():
            async with handle as mmap:
                process(mmap.as_bytes())
```

## 11. Future Enhancements

### Phase 2 (Planned)
- [ ] Write support (MAP_SHARED for persistent changes)
- [ ] Parallel prefaulting for very large files
- [ ] Automatic small file optimization (use read() for <4KB)
- [ ] File watching (reload on change via inotify/kqueue)

### Phase 3 (Considered)
- [ ] io_uring backend for Linux (true async I/O)
- [ ] Direct I/O support (bypass page cache)
- [ ] Compressed file support (transparent decompression)
- [ ] Network file systems (SMB, NFS) optimization

## 12. Related Specifications

- [Concurrency](concurrency.md) - Async/await, futures, actors
- [Memory Management](memory.md) - Ownership, borrowing, lifetimes
- [Functions](functions.md) - Context managers, traits
- [Stdlib](stdlib.md) - Standard library organization

## Revision History

| Version | Date | Changes |
|---------|------|---------|
| 1.0 | 2025-12-26 | Initial specification |
