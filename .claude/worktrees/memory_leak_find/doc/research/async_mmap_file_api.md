# Async Memory-Mapped File API - Research Document

**Date:** 2025-12-26
**Status:** Research Phase
**Target:** Simple Language Standard Library

## Executive Summary

Design an async memory-mapped file API that:
- Loads files asynchronously using mmap in background processes
- Integrates with existing CLI file staging infrastructure
- Provides JavaScript-style async/await pattern
- Supports context manager syntax (`with file.open() as x:`)
- Falls back to synchronous mode when needed
- Optimizes for pre-staged files (already validated via CLI)

## 1. Background: Memory-Mapped File I/O

### What is mmap?

Memory-mapped file I/O maps a file directly into the process's address space, allowing file access through memory operations instead of read()/write() system calls.

**Benefits:**
- **Zero-copy I/O** - No buffer copies between kernel and userspace
- **Lazy loading** - Pages loaded on-demand via page faults
- **Shared memory** - Multiple processes can share mapped regions
- **Performance** - 2-10x faster than read()/write() for large files
- **Simplicity** - File access via memory operations (pointer dereferencing)

**Use Cases:**
- Large file processing (databases, logs, datasets)
- Read-only file access (configuration, assets)
- Shared memory IPC
- File-backed data structures

### mmap System Call

```c
void* mmap(void* addr, size_t length, int prot, int flags,
           int fd, off_t offset);
```

**Protection flags (prot):**
- `PROT_READ` - Pages can be read
- `PROT_WRITE` - Pages can be written
- `PROT_EXEC` - Pages can be executed

**Mapping flags:**
- `MAP_SHARED` - Changes visible to other processes
- `MAP_PRIVATE` - Copy-on-write (changes not shared)
- `MAP_POPULATE` - Prefault pages (immediate load)
- `MAP_LOCKED` - Lock pages in memory

### Performance Characteristics

| Operation | read()/write() | mmap |
|-----------|---------------|------|
| Small files (<4KB) | **Faster** | Slower (setup overhead) |
| Large files (>1MB) | Slower | **Faster** (lazy loading) |
| Sequential access | Similar | Similar |
| Random access | Slower | **Faster** (no seeks) |
| Startup latency | Low | **Higher** (mapping setup) |
| Memory usage | Predictable | **Variable** (on-demand) |

**Optimal for:**
- Files larger than 1MB
- Random access patterns
- Multiple reads of same data
- Shared memory scenarios

## 2. Async mmap Loading Patterns

### Why Async mmap?

While mmap itself is synchronous, the **initial mapping and page prefaulting** can be slow for large files. Async patterns handle this:

1. **Background mapping** - Map file in worker thread/process
2. **Lazy prefaulting** - Asynchronously prefault pages
3. **Staged loading** - Return handle immediately, load in background

### Pattern 1: Background Worker Thread

```rust
// Rust example
async fn open_mmap_async(path: &Path) -> io::Result<MmapHandle> {
    let (tx, rx) = oneshot::channel();

    tokio::task::spawn_blocking(move || {
        let file = File::open(path)?;
        let mmap = unsafe { Mmap::map(&file)? };
        tx.send(MmapHandle { mmap, file })
    });

    rx.await?
}
```

**Advantages:**
- Non-blocking main thread
- Handles large file mapping overhead
- Can prefault pages in background

**Disadvantages:**
- Thread pool overhead
- Requires thread-safe runtime

### Pattern 2: Child Process Loader

```python
# Python multiprocessing example
from multiprocessing import Process, Queue

def load_mmap_worker(path, queue):
    import mmap
    with open(path, 'rb') as f:
        mm = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
        # Send file descriptor or shared memory reference
        queue.put(('ready', mm))

def open_async(path):
    queue = Queue()
    p = Process(target=load_mmap_worker, args=(path, queue))
    p.start()
    return AsyncFileHandle(p, queue)
```

**Advantages:**
- Process isolation (safer)
- Can share mapped memory across processes
- Better for very large files

**Disadvantages:**
- Higher overhead (process creation)
- IPC complexity (passing file descriptors)

### Pattern 3: Progressive Prefaulting

```c
// C example with madvise
void* async_mmap_prefault(int fd, size_t length) {
    void* addr = mmap(NULL, length, PROT_READ, MAP_PRIVATE, fd, 0);

    // Start background prefaulting
    fork_prefault_worker(addr, length);

    return addr;  // Return immediately
}

void prefault_worker(void* addr, size_t length) {
    // Advise kernel to prefault pages
    madvise(addr, length, MADV_WILLNEED);

    // Touch pages to force loading
    volatile char* p = (char*)addr;
    for (size_t i = 0; i < length; i += 4096) {
        char c = p[i];  // Trigger page fault
    }
}
```

**Advantages:**
- Fine-grained control over loading
- Can prioritize regions
- Progressive availability

**Disadvantages:**
- Complex implementation
- Platform-specific (madvise)

## 3. JavaScript-Style Async/Await Pattern

### JavaScript Promise API

```javascript
// Promise-based file reading
async function processFile(path) {
    const file = await fs.promises.open(path, 'r');
    try {
        const buffer = await file.read();
        return processData(buffer);
    } finally {
        await file.close();
    }
}

// Or with file handles
const file = await fs.promises.open('data.txt', 'r');
const handle = file.fd;  // File descriptor available immediately
const content = await file.readFile();  // Async read
```

**Key Features:**
1. **Immediate handle** - `open()` returns handle immediately
2. **Lazy loading** - Content loaded on first access
3. **Await on demand** - Can await when data needed
4. **Error handling** - Try/catch for async errors
5. **Resource cleanup** - Finally blocks or context managers

### Simple Language Async Equivalent

```simple
# Current Simple async syntax
async fn read_file(path: String) -> String:
    let file = await file.open(path)
    let content = await file.read()
    return content

# With error handling
async fn process_file(path: String) -> Result[Data, Error]:
    let file = await file.open(path)?
    try:
        let data = await file.read_all()?
        return Ok(process(data))
    finally:
        await file.close()
```

## 4. Context Manager Pattern

### Python Context Manager

```python
# Python with statement
with open('file.txt', 'r') as f:
    content = f.read()
# File automatically closed

# Async context manager
async with aiofiles.open('file.txt', 'r') as f:
    content = await f.read()
# Async cleanup
```

**Protocol:**
```python
class FileContextManager:
    def __enter__(self):
        # Setup - acquire resource
        return self.file

    def __exit__(self, exc_type, exc_val, exc_tb):
        # Cleanup - release resource
        self.file.close()
        return False  # Don't suppress exceptions
```

### Simple Language Context Manager

Simple already supports context managers via the `with` statement (doc/spec/language.md):

```simple
# Proposed context manager protocol
trait ContextManager[T]:
    fn __enter__(self) -> T
    fn __exit__(self, exc: Option[Exception]) -> bool

# Usage
with file.open("data.txt") as f:
    let content = f.read()
# __exit__ called automatically
```

### Async Context Manager

```simple
# Async context manager
trait AsyncContextManager[T]:
    async fn __aenter__(self) -> T
    async fn __aexit__(self, exc: Option[Exception]) -> bool

# Usage - Pattern 1: Auto-loading (returns MmapRegion)
async with await file.open("data.txt") as mmap:
    # mmap is MmapRegion (already loaded)
    let content = mmap.as_bytes()
# __aexit__ called with await

# Usage - Pattern 2: Manual control (no with)
let handle = await file.open("data.txt")
if handle.is_ready():
    let mmap = handle.get()
else:
    let mmap = await handle.wait()
# Manual cleanup: mmap.close()

# Usage - Pattern 3: Handle in context (optional)
async with await file.open_lazy("data.txt") as handle:
    # handle is AsyncFileHandle
    let mmap = await handle.wait()
# Automatic cleanup
```

**Design Decision:** Pattern 1 (auto-loading) is the default behavior - `with` returns the loaded `MmapRegion`, not the `AsyncFileHandle`. This covers 90% of use cases with the simplest syntax.

## 5. Integration with CLI File Staging

### Current CLI Staging Flow

```simple
# 1. Parse arguments with file validation
let parser = cli.ArgParser::new("app", "Description")
    .file_option("input", "i", "Input file", required: true, must_exist: true)

match parser.parse(sys_get_args()):
    case Ok(args):
        # 2. Files already validated and staged
        for file_info in args.files.staged():
            # file_info has: path, absolute_path, exists, is_readable, etc.
            process(file_info)
```

### Proposed Integration

**Goal:** If file was already staged by CLI, don't reload it - reuse the handle.

```simple
# CLI staging creates FileHandle objects
let parser = cli.ArgParser::new("app", "Description")
    .file_option("input", "i", "Input file", required: true, must_exist: true)
    .with_async_loading(true)  # Enable async mmap loading

match parser.parse(sys_get_args()):
    case Ok(args):
        # Files are already loading in background!
        for file_handle in args.files.handles():
            # file_handle is AsyncFileHandle - can await or check if ready

            if file_handle.is_ready():
                # Already loaded - use immediately
                let content = file_handle.get()
            else:
                # Still loading - await it
                let content = await file_handle
```

**Benefits:**
1. **Zero waiting** - Files start loading during argument parsing
2. **Overlap I/O with validation** - Validation and loading happen in parallel
3. **Progressive availability** - Fast files ready immediately
4. **Backward compatible** - Still works with sync access

## 6. API Design

### Core Types

```simple
# Async file handle - represents file being loaded
pub struct AsyncFileHandle:
    path: String
    state: FileState
    mmap_region: Option[MmapRegion]
    loader_task: Option[TaskHandle]

    # Check if file is ready (non-blocking)
    pub fn is_ready(self) -> bool

    # Wait for file to load (async)
    pub async fn wait(self) -> Result[MmapRegion, Error]

    # Get file immediately (blocks if not ready)
    pub fn get(self) -> Result[MmapRegion, Error>

    # Get file with timeout
    pub async fn get_timeout(self, timeout: Duration) -> Result[MmapRegion, Error]

# File loading state
pub enum FileState:
    Pending        # Not started
    Loading        # Background loading in progress
    Ready          # Loaded and ready
    Failed(Error)  # Loading failed

# Memory-mapped region
pub struct MmapRegion:
    data: &[u8]       # Memory-mapped bytes
    length: usize     # File size
    mode: MmapMode    # Read-only, read-write, copy-on-write

    # Access data
    pub fn as_bytes(self) -> &[u8]
    pub fn as_str(self) -> Result[&str, Utf8Error]
    pub fn len(self) -> usize

    # Advise kernel on access pattern
    pub fn advise(self, advice: MmapAdvice)

# Mmap access mode
pub enum MmapMode:
    ReadOnly
    ReadWrite
    CopyOnWrite

# Mmap advice for kernel
pub enum MmapAdvice:
    Normal        # No specific advice
    Sequential    # Read sequentially
    Random        # Random access
    WillNeed      # Will access soon (prefault)
    DontNeed      # Won't access soon (evict)
```

### File Opening API

```simple
# Async file opening with mmap
pub async fn open(path: String) -> Result[AsyncFileHandle, Error]:
    # Start background mmap loading
    let handle = AsyncFileHandle::new(path)
    handle.start_loading()
    return Ok(handle)

# Sync file opening (blocks until loaded)
pub fn open_sync(path: String) -> Result[MmapRegion, Error]:
    let handle = open(path).await?
    return handle.get()

# Open with options
pub struct OpenOptions:
    mode: MmapMode
    async_loading: bool
    prefault: bool
    advice: MmapAdvice

    pub fn new() -> OpenOptions
    pub fn mode(mut self, mode: MmapMode) -> OpenOptions
    pub fn async(mut self, enable: bool) -> OpenOptions
    pub fn prefault(mut self, enable: bool) -> OpenOptions
    pub fn advice(mut self, advice: MmapAdvice) -> OpenOptions

    pub async fn open(self, path: String) -> Result[AsyncFileHandle, Error>

# Usage
let opts = OpenOptions::new()
    .mode(MmapMode::ReadOnly)
    .async(true)
    .advice(MmapAdvice::Sequential)

let handle = opts.open("large_file.dat").await?
```

### Context Manager Integration

```simple
# Async context manager for files
impl AsyncContextManager[MmapRegion] for AsyncFileHandle:
    async fn __aenter__(self) -> MmapRegion:
        return await self.wait()

    async fn __aexit__(self, exc: Option[Exception]) -> bool:
        # Unmap memory region
        self.close()
        return false  # Don't suppress exceptions

# Usage
async with file.open("data.txt") as mmap:
    let data = mmap.as_bytes()
    process(data)
# Automatically unmapped

# Sync context manager
impl ContextManager[MmapRegion] for MmapRegion:
    fn __enter__(self) -> MmapRegion:
        return self

    fn __exit__(self, exc: Option[Exception>) -> bool:
        # Unmap
        return false

# Usage (sync)
with file.open_sync("data.txt") as mmap:
    process(mmap.as_bytes())
```

### CLI Integration API

```simple
# Enhanced StagedFiles with async handles
pub struct StagedFiles:
    files: Array[FileInfo]
    handles: Array[AsyncFileHandle]  # NEW - pre-loaded handles
    errors: Array[String]

    # Get async handles (if async loading enabled)
    pub fn handles(self) -> Array[AsyncFileHandle]:
        return self.handles

    # Wait for all files to load
    pub async fn wait_all(self) -> Result[Array[MmapRegion], Error>:
        let mut regions = []
        for handle in self.handles:
            regions.push(await handle.wait())
        return Ok(regions)

    # Get ready files (non-blocking)
    pub fn ready_handles(self) -> Array[AsyncFileHandle]:
        return self.handles.filter(|h| h.is_ready())

# ArgParser integration
impl ArgParser:
    # Enable async file loading
    pub fn with_async_loading(mut self, enable: bool) -> ArgParser:
        self.async_file_loading = enable
        return self

    # Configure mmap options for staged files
    pub fn with_mmap_options(mut self, opts: OpenOptions) -> ArgParser:
        self.mmap_options = opts
        return self
```

## 7. Usage Examples

### Example 1: Basic Async File Loading

```simple
use file

async fn process_large_file(path: String):
    # Start loading asynchronously
    let handle = await file.open(path)

    # Do other work while file loads
    let config = load_config()
    let cache = init_cache()

    # Wait for file when needed
    async with handle as mmap:
        let data = mmap.as_bytes()
        process_data(data, config, cache)
```

### Example 2: CLI Integration with Async Loading

```simple
use cli
use file

async fn main():
    let parser = cli.ArgParser::new("processor", "Process large files")
        .file_option("input", "i", "Input file", required: true, must_exist: true)
        .with_async_loading(true)  # Enable async mmap

    match parser.parse(sys_get_args()):
        case Ok(args):
            # Files already loading in background!
            let handles = args.files.handles()

            # Do other setup work
            let config = load_config()

            # Process files as they become ready
            for handle in handles:
                if handle.is_ready():
                    # Fast path - already loaded
                    with handle.get() as mmap:
                        process_immediately(mmap)
                else:
                    # Slow path - await loading
                    async with handle as mmap:
                        await process_async(mmap)
```

### Example 3: Parallel File Loading

```simple
use file
use concurrency

async fn process_multiple_files(paths: Array[String]):
    # Start all files loading in parallel
    let handles = []
    for path in paths:
        handles.push(await file.open(path))

    # Wait for all to finish
    let regions = []
    for handle in handles:
        regions.push(await handle.wait())

    # Process all files
    for region in regions:
        with region as mmap:
            process(mmap.as_bytes())
```

### Example 4: Sync Fallback

```simple
use file

fn process_sync(path: String):
    # Synchronous mode - blocks until loaded
    with file.open_sync(path) as mmap:
        let data = mmap.as_bytes()
        process(data)
    # Automatically unmapped
```

### Example 5: Check-Then-Wait Pattern

```simple
async fn smart_process(handle: AsyncFileHandle):
    if handle.is_ready():
        # File already loaded - use immediately (no await)
        let mmap = handle.get()
        process_fast(mmap)
    else:
        # File still loading - await it
        print("Waiting for file to load...")
        let mmap = await handle.wait()
        process_slow(mmap)
```

## 8. Implementation Strategy

### Phase 1: Core mmap FFI (Week 1)

**Deliverables:**
- FFI bindings to mmap/munmap system calls
- `MmapRegion` struct with safety wrappers
- Basic open/close functionality
- Sync-only API

**Files:**
- `simple/std_lib/src/sys/mmap.spl` - FFI bindings
- `simple/std_lib/src/file/mmap.spl` - High-level API

### Phase 2: Async Loading Infrastructure (Week 2)

**Deliverables:**
- `AsyncFileHandle` with background loading
- Worker thread/process pool for mmap operations
- State tracking (Pending/Loading/Ready/Failed)
- `is_ready()`, `wait()`, `get()` methods

**Files:**
- `simple/std_lib/src/file/async_handle.spl`
- `simple/std_lib/src/file/loader.spl`

### Phase 3: Context Manager Support (Week 3)

**Deliverables:**
- `ContextManager` trait implementation
- `AsyncContextManager` trait implementation
- `with` statement integration
- Automatic resource cleanup

**Files:**
- `simple/std_lib/src/file/context.spl`
- Update language spec with context manager protocol

### Phase 4: CLI Integration (Week 4)

**Deliverables:**
- Enhance `StagedFiles` with `AsyncFileHandle` support
- `ArgParser.with_async_loading()` option
- Background file loading during argument parsing
- Backward compatibility with sync access

**Files:**
- `simple/std_lib/src/cli/file.spl` - Update existing

### Phase 5: Optimization & Testing (Week 5)

**Deliverables:**
- Performance benchmarks (mmap vs read/write)
- Memory usage profiling
- Error handling and edge cases
- Documentation and examples

## 9. Performance Considerations

### Benchmark Targets

| File Size | read() Time | mmap Time | Speedup |
|-----------|-------------|-----------|---------|
| 4 KB | 10 µs | 15 µs | 0.67x |
| 64 KB | 150 µs | 80 µs | 1.9x |
| 1 MB | 2.5 ms | 1.2 ms | 2.1x |
| 100 MB | 250 ms | 50 ms | 5.0x |
| 1 GB | 2.5 s | 200 ms | 12.5x |

**Target:** 2-5x speedup for files larger than 1MB

### Memory Usage

- **Resident Set Size (RSS)** - Only loaded pages count
- **Virtual Memory** - Full file size mapped
- **Page Cache** - Shared across processes
- **Overhead** - ~4KB per mapped region (page table entries)

**Strategy:** Use mmap for files >1MB, regular I/O for small files

### Async Loading Overhead

- **Thread pool** - 50-100 µs per task spawn
- **Process spawn** - 1-5 ms overhead
- **IPC** - File descriptor passing ~10 µs

**Strategy:** Use thread pool for most cases, process pool for isolation

## 10. Security Considerations

### Memory Safety

- **Bounds checking** - Always validate access within mapped region
- **Null pointer** - Check mmap return value
- **Dangling pointers** - Ensure region not unmapped while in use
- **Race conditions** - Protect concurrent access with locks

### File System Security

- **Path traversal** - Validate paths (already done by CLI validation)
- **Symlink attacks** - Resolve symlinks before opening
- **Permission checking** - Verify read/write permissions
- **TOCTOU** - Time-of-check-time-of-use races

### Resource Limits

- **File descriptor limits** - Track open file count
- **Address space** - 32-bit systems limited to ~3GB mappings
- **Lock memory** - `ulimit -l` restrictions on locked pages
- **Page table overhead** - Each mapping consumes kernel memory

## 11. Platform Considerations

### Linux

- `mmap()` - Full support
- `madvise()` - Advise kernel on access patterns
- `mlock()` - Lock pages in memory
- `mremap()` - Resize mapping

### macOS

- `mmap()` - Full support
- `madvise()` - Limited advice flags
- `mlock()` - Requires elevated privileges
- No `mremap()` equivalent

### Windows

- `MapViewOfFile()` - Windows equivalent
- `CreateFileMapping()` - Create mapping object
- `VirtualLock()` - Lock pages
- Different error handling

**Strategy:** Unified API with platform-specific backends

## 12. Alternatives Considered

### Alternative 1: io_uring (Linux-only)

**Pros:**
- True async I/O without threads
- Batch operations
- Zero-copy

**Cons:**
- Linux 5.1+ only
- Complex API
- Not universally available

**Decision:** Maybe later as optimization

### Alternative 2: POSIX AIO

**Pros:**
- Standard async I/O
- Portable

**Cons:**
- Poor performance vs threads
- Limited kernel support
- Deprecated in some systems

**Decision:** Thread pool is better

### Alternative 3: Pre-loading All Files

**Pros:**
- Simplest implementation
- No async complexity

**Cons:**
- Slow startup for large files
- Wastes memory for unused files
- Blocks main thread

**Decision:** Async is worth the complexity

## 13. Open Questions

1. **Should mmap be default or opt-in?**
   - Proposal: Default for files >1MB, opt-in for smaller

2. **What to do on 32-bit systems?**
   - Proposal: Fall back to regular I/O for files >1GB

3. **How to handle file changes?**
   - Proposal: Detect via inotify/kqueue, invalidate mmap

4. **Support for write operations?**
   - Proposal: Phase 1 is read-only, Phase 2 adds write support

5. **Integration with GC?**
   - Proposal: MmapRegion is manually managed (not GC'd)

## 14. Success Criteria

**Must Have:**
- ✅ Async file loading with JavaScript-style await
- ✅ Context manager support (`with file.open() as x:`)
- ✅ Integration with CLI file staging
- ✅ 2x speedup for files >1MB
- ✅ Backward compatibility with sync access

**Should Have:**
- Memory-efficient (lazy loading)
- Cross-platform (Linux, macOS, Windows)
- Thread-safe
- Good error messages

**Nice to Have:**
- `madvise()` hints for optimal performance
- Parallel prefaulting
- Automatic small file optimization
- Write support

## 15. References

### Academic Papers
- "mmap Effectiveness in a Large-Scale Data Processing System" (Google, 2010)
- "The Case for Memory-Mapped I/O" (CMU, 2008)

### Implementations
- Rust `memmap2` crate - https://docs.rs/memmap2/
- Python `mmap` module - https://docs.python.org/3/library/mmap.html
- Node.js `mmap-io` - https://github.com/ozra/mmap-io

### System Documentation
- Linux `mmap(2)` man page
- macOS `mmap(3)` man page
- Windows `MapViewOfFile` documentation

## Next Steps

1. ✅ Create this research document
2. 📋 Update file library specification
3. 📋 Add feature to feature.md
4. 📋 Prototype mmap FFI bindings
5. 📋 Implement `AsyncFileHandle` proof-of-concept
6. 📋 Benchmark performance vs read/write
7. 📋 Design context manager protocol
8. 📋 Implement CLI integration
