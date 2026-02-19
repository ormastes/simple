# Library Variant Architecture Plan

**Date:** 2026-02-19
**Status:** Draft - Research & Architecture
**Prereqs:** `doc/plan/manual_memory_safety_plan.md`, `doc/design/baremetal_async_resources_v0.3.md`, `doc/feature/async_implementation_status.md`

---

## 0) Problem Statement

The current `src/lib/` is a flat 128-module monolith (1,123 .spl files). Every module is available regardless of target profile (GC/no-GC, sync/async, heap/no-heap). This causes:

1. **Baremetal code pulls in heap-dependent modules** - Embedded targets cannot use fileio/network without pulling GC runtime
2. **No sync alternative** - All IO is blocking-sync under the hood (FFI calls) but no first-class async IO exists
3. **Unique vs GC pointer ambiguity** - Code written for GC doesn't know if it can work with unique pointers
4. **Portability gap** - No way to write code that works across sync/async without rewriting

### Goal

Split `src/lib/` into **profile-aware library variants** so that:
- Code written for `nogc_sync_mut` (unique pointers, blocking IO) **automatically works** in `gc_async_mut` (GC pointers, async IO)
- Baremetal code uses `nogc_async_mut_noalloc` with zero heap, compile-time verified resources
- The API surface is **nearly identical** across all variants

---

## 1) Research Summary

### 1.1 Rust Patterns

| Pattern | How Tokio/Embassy Do It | Applicability |
|---------|------------------------|---------------|
| **Parallel modules** | `std::fs` vs `tokio::fs` - same names, async return types | Core strategy for sync/async split |
| **Poll-based futures** | `Future::poll() -> Poll<T>` with lazy evaluation | Already implemented in `async_core.spl` |
| **spawn_blocking** | File IO dispatched to thread pool (not truly async) | Needed for `nogc_async_mut` file IO |
| **Embassy no-alloc** | Static task allocation, compile-time sizing | Maps to `nogc_async_mut_noalloc` |
| **Send/Sync traits** | `Send` = transferable between threads, `Sync` = sharable | Maps to pointer capabilities (`iso`, `mut`, shared) |

### 1.2 TypeScript/Node.js Patterns

| Pattern | How Node Does It | Applicability |
|---------|-----------------|---------------|
| **Three API surfaces** | Callback, sync (`readFileSync`), promise (`fs/promises`) | Validates the multi-surface approach |
| **Streams as async iterators** | `for await (const chunk of stream)` | `for~ chunk in stream:` syntax |
| **AbortController** | Cooperative cancellation via signal | Maps to `CancellationToken` (already exists) |

### 1.3 Current Simple Async Status

- **Parser:** Complete (async/await/spawn keywords)
- **Desugaring:** Complete (state machine generation)
- **Core Type System:** NOT integrated (Future<T>, Poll<T>, Task types missing at runtime)
- **Runtime libraries:** Complete (async_embedded, async_host, async_core, async_unified)
- **Tests:** 38+ files, ALL SKIPPED (runtime parser doesn't support async keywords)
- **Conclusion:** Libraries are written but **0% executable**. Type system bridge is the blocker.

### 1.4 Current Pointer Types (from memory_safety_plan.md)

| Syntax | Name | GC? | Mutation |
|--------|------|-----|----------|
| `T` | GC Reference | Yes | Via `mut` |
| `&T` | Unique | No (RAII) | Via `mut` |
| `*T` | Shared | No (RC) | Read-only |
| `-T` | Weak | No | N/A |
| `+T` | Handle | Pool | Via pool |

**Key insight:** Code using `&T` (unique) is a strict subset of code using `T` (GC). If it compiles with `&T`, it will compile with `T`. This is the portability guarantee.

---

## 2) Architecture: Library Variant System

### 2.1 Variant Matrix

```
                    ┌───────────┬────────────┬────────────────────┐
                    │  sync_mut │ async_mut  │ async_mut_noalloc  │
┌───────────────────┼───────────┼────────────┼────────────────────┤
│ nogc (unique ptr) │ VARIANT 1 │ VARIANT 2  │ VARIANT 3          │
│ gc (gc ptr)       │     -     │ VARIANT 4  │         -          │
└───────────────────┴───────────┴────────────┴────────────────────┘
```

| Variant | Directory | Pointer Default | IO Model | Heap | Target |
|---------|-----------|----------------|----------|------|--------|
| **common** | `lib/common/` | None (pure logic) | None | Optional | All |
| **V1: nogc_sync_mut** | `lib/nogc_sync_mut/` | `&T` (unique) | Blocking sync | Yes | CLI tools, scripts |
| **V2: nogc_async_mut** | `lib/nogc_async_mut/` | `&T` (unique) | Async (host runtime) | Yes | Servers, apps |
| **V3: nogc_async_mut_noalloc** | `lib/nogc_async_mut_noalloc/` | `&T` (unique) | Async (embedded) | No | Baremetal, RTOS |
| **V4: gc_async_mut** | `lib/gc_async_mut/` | `T` (GC) | Async (host runtime) | Yes | Default, rapid dev |

**No `gc_sync_mut`:** GC implies a runtime with event loops. Sync+GC is just V4 with `block_on()`.

### 2.2 Dependency Hierarchy

```
common (pure, no IO, no pointers)
  ├── nogc_sync_mut (blocking IO, unique ptrs)
  │     └── nogc_async_mut (async IO wrapping sync, unique ptrs)
  │           ├── nogc_async_mut_noalloc (static alloc, embedded async)
  │           └── gc_async_mut (GC ptrs, full runtime)
```

**Rule: Each variant imports everything from its parent.** Code written for V1 works in V2/V4. Code for V2 works in V4.

### 2.3 What Goes Where

#### `common/` - Pure Logic (no IO, no allocation preference)

Modules that are pure computation with no side effects:
- `math/`, `complex/`, `fraction/`, `geometry/`
- `sorting/`, `iterator/`, `lazy/`, `pipeline/`
- `json/`, `sdn/`, `xml/`, `yaml/`, `csv/`, `msgpack/` (parsing/serialization)
- `regex/`, `regex_engine/`, `fsm/`
- `base64/`, `base_encoding/`, `huffman/`, `lz77/`
- `text/` (string operations), `date/` (formatting), `color/`
- `diff/`, `template/`, `uri/`, `html/`, `markdown/`
- `type/`, `types/`, `core/`
- `serialize/` (trait definitions)
- `collections/`, `map/`, `linked_list/`, `queue/`, `rope/`
- All tree structures: `avl_tree/`, `b_tree/`, `red_black_tree/`, `kd_tree/`, etc.
- `graph/`, `union_find/`, `bloom_filter/`, `trie/`, `skip_list/`
- `statistics/`, `numerical_methods/`, `linear_algebra/`, `fft/`
- `optimization/`, `signal_processing/`
- `crypto/` (pure algorithm parts), `aes/`, `rsa/`, `bcrypt/`, `scrypt/`
- `report/`, `diagnostics/` (formatting only)
- `locale/`, `i18n/`
- `common/` (config, target, diagnostics - existing)
- `async_core/` (Poll, TaskState, Priority, CancellationToken - already pure)

#### `nogc_sync_mut/` - Blocking IO with Unique Pointers

Everything in `common/` plus:
- `fs/` - Sync file operations (`fn read_text(path: text) -> Result<text, IoError>`)
- `file_system/` - Sync directory ops, metadata, permissions, watch
- `net/` - Sync TCP/UDP (`fn connect(addr: text) -> Result<TcpStream, IoError>`)
- `http/`, `http_client/`, `http_server/` - Sync HTTP
- `dns/` - Sync DNS resolution
- `tls/` - Sync TLS
- `ffi/` - All sync FFI bindings (current `rt_*` functions)
- `io_runtime/` - Sync IO runtime wrapper
- `env/` - Environment variables
- `cli/` - CLI parsing
- `shell/` - Process execution
- `binary_io/` - Binary read/write
- `buffer/` - Buffered IO
- `compress/`, `compression/` - Compression (needs file IO)
- `cache/` - Caching (needs file or memory IO)
- `database/` - DB operations
- `benchmark/` - Benchmarking (needs timing IO)
- `testing/`, `test/`, `spec/` - Test infrastructure

#### `nogc_async_mut/` - Async IO with Unique Pointers

Everything in `nogc_sync_mut/` plus async wrappers:
- `async/` - Async runtime (current `async/` subdir)
- `async_host/` - Host runtime (work-stealing, wakers)
- `async_unified/` - Unified async API
- `fs/` **overrides** sync with async: `async fn read_text(path: text) -> Result<text, IoError>`
- `net/` **overrides** sync with async: `async fn connect(addr: text) -> Result<TcpStream, IoError>`
- `http_client/` **overrides** with async HTTP
- `http_server/` **overrides** with async HTTP server
- `websocket/` - Async WebSocket
- `mqtt/`, `kafka/`, `stomp/` - Async messaging
- `smtp/` - Async email
- `oauth/` - Async OAuth
- `concurrent/` - Concurrent data structures
- `actors/` - Actor model

#### `nogc_async_mut_noalloc/` - Baremetal Async

Subset of `nogc_async_mut/` with no heap:
- `async_embedded/` - Embedded runtime (fixed capacity, polling)
- `baremetal/` - Architecture backends (arm, x86, riscv, etc.)
- `execution/` - Semihost capture, string table
- `memory/` - Manual memory management
- `qemu/` - QEMU runner
- Resource-limited versions of IO via semihosting
- Follows `baremetal_async_resources_v0.3.md` design

#### `gc_async_mut/` - Full GC Runtime (Default)

Everything in `nogc_async_mut/` with GC semantics:
- Default pointer type is `T` (GC-managed) instead of `&T` (unique)
- `pure/` - ML tensor library (needs GC for graph-based autograd)
- `cuda/`, `torch/` - GPU bindings (GC manages device memory)
- `gpu/`, `gpu_runtime/` - GPU runtime
- Additional convenience APIs that assume GC (e.g., auto-closing file handles)

---

## 3) Sync/Async API Portability Design

### 3.1 Core Principle: Same Signature, Different Effect

Following the Tokio model: async version has **identical function names and parameter types**, differing only in the async marker and return wrapping.

```simple
# --- nogc_sync_mut/fs.spl ---
fn read_text(path: text) -> Result<text, IoError>:
    val raw = rt_file_read_text(path)
    if raw == "": Err(IoError.NotFound(path))
    else: Ok(raw)

fn write_text(path: text, content: text) -> Result<(), IoError>:
    if rt_file_write_text(path, content): Ok(())
    else: Err(IoError.WriteFailed(path))

# --- nogc_async_mut/fs.spl ---
async fn read_text(path: text) -> Result<text, IoError>:
    # Dispatched to blocking thread pool (like tokio::fs)
    spawn_blocking(\: sync_fs.read_text(path))~=

async fn write_text(path: text, content: text) -> Result<(), IoError>:
    spawn_blocking(\: sync_fs.write_text(path, content))~=
```

### 3.2 User Code Portability

```simple
# This function works in BOTH sync and async contexts.
# In sync mode, read_text blocks. In async mode, it suspends.
fn process_config(path: text) -> Result<Config, IoError>:
    val content = read_text(path)?
    val config = parse_sdn(content)?
    Ok(config)
```

The compiler resolves `read_text` to the correct variant based on the active library profile. The `?` operator works identically in both.

### 3.3 Network API Portability

```simple
# --- nogc_sync_mut/net/tcp.spl ---
fn connect(addr: text) -> Result<TcpStream, NetError>:
    tcp_stream_connect(addr)

fn read(stream: TcpStream, size: usize) -> Result<[u8], NetError>:
    tcp_stream_read(stream, size)

# --- nogc_async_mut/net/tcp.spl ---
async fn connect(addr: text) -> Result<TcpStream, NetError>:
    # Uses epoll/kqueue/IOCP under the hood
    async_tcp_stream_connect(addr)~=

async fn read(stream: TcpStream, size: usize) -> Result<[u8], NetError>:
    async_tcp_stream_read(stream, size)~=
```

### 3.4 Stream API (Async Only)

```simple
# Async streams for large data (only in async variants)
async fn read_stream(path: text) -> AsyncIterator<Result<[u8], IoError>>:
    val file = open(path)~=?
    async for chunk in file.chunks(4096):
        yield chunk

# Usage:
for~ chunk in read_stream("large_file.bin"):
    process(chunk?)
```

### 3.5 Profile Selection

In `simple.sdn` (project config):

```sdn
build:
  lib_profile: gc_async_mut       # Default for applications
  # lib_profile: nogc_sync_mut    # For CLI tools
  # lib_profile: nogc_async_mut   # For servers without GC
  # lib_profile: nogc_async_mut_noalloc  # For baremetal
```

Compiler resolves imports based on profile:
```simple
use std.fs.read_text   # Resolves to the profile's fs module
use std.net.tcp        # Resolves to the profile's tcp module
```

---

## 4) Pointer Portability: Unique -> GC Guarantee

### 4.1 Core Rule

> **If code compiles with `&T` (unique pointer), it compiles with `T` (GC pointer).**

This is because unique pointers are a **strict subset** of GC capabilities:

| Operation | `&T` (unique) | `T` (GC) |
|-----------|--------------|-----------|
| Read field | Yes | Yes |
| Mutate (with `mut`) | Yes | Yes |
| Pass to function | Move (transfer ownership) | Copy (share reference) |
| Store in collection | Move into | Copy into |
| Return from function | Move out | Copy out |
| Multiple references | No (compile error) | Yes |

### 4.2 How This Works in Practice

```simple
# nogc profile: &T is default
fn process(data: &MyStruct):  # Takes ownership, single owner
    val result = transform(data)  # data moved to transform
    # data is no longer valid here

# gc profile: T is default
fn process(data: MyStruct):  # GC reference, can be shared
    val result = transform(data)  # data shared with transform
    # data is still valid here (GC manages lifetime)
```

**The same source code works in both profiles** because:
1. `nogc` profile: compiler infers `&T` for unqualified `T`, enforces move semantics
2. `gc` profile: compiler uses GC-managed `T`, allows implicit sharing

### 4.3 Explicit Opt-Out

When code needs GC-specific behavior (multiple references):

```simple
# This only works in gc profile
fn share_ref(data: T) -> (T, T):
    (data, data)  # Two references to same object - requires GC
```

Use `@when(profile.gc)` for GC-specific code:

```simple
@when(profile.gc)
fn share_ref(data: T) -> (T, T):
    (data, data)

@when(profile.nogc)
fn share_ref(data: &T) -> (&T, &T):
    val clone = data.clone()
    (data, clone)
```

---

## 5) SDoctest: Compiler Config in Interpreter

### 5.1 Problem

SDoctest runs code blocks via subprocess: `bin/simple <temp_file.spl>`. This uses the interpreter by default. But documentation examples should demonstrate **compiled** behavior (async/await, generics, etc. that only work compiled).

### 5.2 Current Run-Config Mechanism

Already partially implemented:
- Fence modifier: `` ```simple:@native ``
- HTML comment: `<!--sdoctest:@native-->`
- Config file: `environments.native.run-config: "native"`

The `--run-config=` flag is passed to the subprocess but **the runtime doesn't fully handle all configs**.

### 5.3 Solution: Profile-Aware SDoctest

1. **Add `@compiled` modifier** for blocks that need compilation:
   ```markdown
   ```simple:@compiled
   async fn fetch() -> i64:
       val data = read_text("config.sdn")~=
       parse_int(data)?
   ```
   ```

2. **Add `@profile=<name>` modifier** for profile-specific blocks:
   ```markdown
   ```simple:@profile=nogc_sync_mut
   val file = read_text("data.txt")?
   print file
   ```
   ```

3. **Runner changes** (in `sdoctest/runner.spl`):
   ```simple
   val run_args = match block.get_run_config():
       case "compiled": ["build", "--run", temp_path]
       case "native": ["build", "--release", "--run", temp_path]
       case "": [temp_path]  # Default: interpreter
       case rc: ["--run-config={rc}", temp_path]
   ```

4. **Profile propagation**:
   ```simple
   if block.has_modifier("profile"):
       val profile = block.get_modifier_value("profile")
       run_args.insert(0, "--lib-profile={profile}")
   ```

---

## 6) Directory Structure

### 6.1 New `src/lib/` Layout

```
src/lib/
  common/                           # Pure logic (existing + moved modules)
    __init__.spl                    # Re-exports
    config_env.spl                  # (existing)
    diagnostic.spl                  # (existing)
    target.spl                      # (existing)
    ...                             # (existing common/ files)
    math/                           # Moved from lib/math/
    json/                           # Moved from lib/json/
    collections/                    # Moved from lib/collections/
    text/                           # Moved from lib/text/
    ...                             # All pure-logic modules
    async_core/                     # Poll, TaskState, CancellationToken
    error/                          # Error types (IoError, NetError, etc.)

  nogc_sync_mut/                    # Blocking IO, unique pointers
    __init__.spl
    fs/                             # Sync file operations
      __init__.spl
      read.spl                      # read_text, read_bytes, read_lines
      write.spl                     # write_text, write_bytes, append_text
      path.spl                      # Path operations
      dir.spl                       # Directory operations
      metadata.spl                  # File metadata
      watch.spl                     # File watching
    net/                            # Sync networking
      __init__.spl
      tcp.spl                       # TcpListener, TcpStream
      udp.spl                       # UdpSocket
      dns.spl                       # DNS resolution
    http/                           # Sync HTTP
      __init__.spl
      client.spl                    # HTTP client
      server.spl                    # HTTP server
      request.spl
      response.spl
    io/                             # IO primitives
      __init__.spl
      buffer.spl                    # Buffered reader/writer
      binary.spl                    # Binary IO
      stream.spl                    # Sync stream traits (Reader, Writer)
    ffi/                            # Sync FFI bindings
      __init__.spl
      io.spl                        # File FFI (current rt_file_* functions)
      system.spl                    # System FFI
      net.spl                       # Network FFI (current tcp_*/udp_* functions)
    env/                            # Environment
    cli/                            # CLI parsing
    shell/                          # Process execution
    tls/                            # Sync TLS
    database/                       # Database operations
    compress/                       # Compression
    cache/                          # Caching
    testing/                        # Test infrastructure
    benchmark/                      # Benchmarking

  nogc_async_mut/                   # Async IO, unique pointers
    __init__.spl
    fs/                             # Async file operations (wraps sync via spawn_blocking)
      __init__.spl
      read.spl
      write.spl
      path.spl                      # Re-exports from sync (paths are not async)
      dir.spl
      stream.spl                    # AsyncReader, file streaming
    net/                            # Async networking
      __init__.spl
      tcp.spl                       # Async TcpListener, TcpStream
      udp.spl                       # Async UdpSocket
      dns.spl                       # Async DNS
    http/                           # Async HTTP
      __init__.spl
      client.spl                    # Async HTTP client
      server.spl                    # Async HTTP server
    io/                             # Async IO primitives
      __init__.spl
      stream.spl                    # AsyncReader, AsyncWriter traits
      buffer.spl                    # Async buffered IO
    runtime/                        # Async runtime
      __init__.spl
      executor.spl                  # Task executor
      scheduler.spl                 # Work-stealing scheduler
      waker.spl                     # Waker mechanism
      worker_thread.spl             # Thread pool
      joinset.spl                   # Structured concurrency
      futures_unordered.spl         # Streaming completion
    future/                         # Future types
      __init__.spl
      core.spl                      # HostFuture<T>
      promise.spl                   # HostPromise<T>
      combinators.spl               # join_all, select, race, timeout
    websocket/                      # Async WebSocket
    mqtt/                           # Async MQTT
    kafka/                          # Async Kafka
    smtp/                           # Async SMTP
    actors/                         # Actor model
    concurrent/                     # Concurrent data structures

  nogc_async_mut_noalloc/           # Baremetal async, no heap
    __init__.spl
    runtime/                        # Embedded async runtime
      __init__.spl
      executor.spl                  # Fixed-capacity executor
      scheduler.spl                 # Cooperative scheduler
      future.spl                    # EmbeddedFuture (stack-based)
      promise.spl                   # EmbeddedPromise
    resource/                       # Compile-time verified resources
      __init__.spl
      pool.spl                      # resource pool
      queue.spl                     # resource queue
      set.spl                       # resource set
      dict.spl                      # resource dict
    io/                             # Semihost IO
      __init__.spl
      semihost.spl                  # Semihosting read/write
      serial.spl                    # Serial port
    baremetal/                       # Architecture backends
      arm/
      arm64/
      x86/
      x86_64/
      riscv/
      riscv32/
      common/
    memory/                         # Manual memory management
    qemu/                           # QEMU runner

  gc_async_mut/                     # GC runtime, async IO (default)
    __init__.spl
    # Mostly re-exports from nogc_async_mut with GC pointer semantics
    # Plus GC-specific modules:
    pure/                           # ML tensor library
    cuda/                           # CUDA GPU
    torch/                          # PyTorch bindings
    gpu/                            # GPU runtime
    gc/                             # GC-specific utilities
      __init__.spl
      auto_close.spl               # Auto-closing handles
      finalizer.spl                # GC finalizers
      weak_ref.spl                 # Weak references
```

### 6.2 Import Resolution

The compiler maps `use std.X` based on the active profile:

```
Profile: gc_async_mut (default)
  use std.fs        -> lib/nogc_async_mut/fs/ (async, overridden by gc_async_mut if exists)
  use std.net       -> lib/nogc_async_mut/net/
  use std.math      -> lib/common/math/
  use std.pure      -> lib/gc_async_mut/pure/

Profile: nogc_sync_mut
  use std.fs        -> lib/nogc_sync_mut/fs/ (sync)
  use std.net       -> lib/nogc_sync_mut/net/ (sync)
  use std.math      -> lib/common/math/
  use std.pure      -> ERROR: pure/ requires gc profile
```

**Resolution order** (for profile `gc_async_mut`):
1. `lib/gc_async_mut/X/` (profile-specific override)
2. `lib/nogc_async_mut/X/` (parent)
3. `lib/nogc_sync_mut/X/` (grandparent)
4. `lib/common/X/` (base)

### 6.3 Explicit Cross-Profile Imports

```simple
# Force sync version even in async profile
use std.nogc_sync_mut.fs as sync_fs
val content = sync_fs.read_text("config.sdn")  # Blocks

# Force async version
use std.nogc_async_mut.fs as async_fs
val content = async_fs.read_text("config.sdn")~=  # Suspends
```

---

## 7) Async Redesign: FileIO and Network

### 7.1 Async File IO Architecture

**Problem:** Most OSes have no truly async file IO. Linux has `io_uring`, others don't.

**Solution (following Tokio):**

```
Layer 1: Sync FFI (existing rt_file_* functions)
Layer 2: Sync wrapper (nogc_sync_mut/fs/)
Layer 3: Async wrapper via spawn_blocking (nogc_async_mut/fs/)
Layer 4: io_uring fast path (future, Linux-only, behind @when)
```

```simple
# nogc_async_mut/fs/read.spl

use std.nogc_sync_mut.fs as sync_fs
use std.nogc_async_mut.runtime.worker_thread.spawn_blocking

async fn read_text(path: text) -> Result<text, IoError>:
    """Read file contents as text (async via thread pool)."""
    spawn_blocking(\: sync_fs.read_text(path))~=

async fn read_bytes(path: text) -> Result<[u8], IoError>:
    """Read file contents as bytes (async via thread pool)."""
    spawn_blocking(\: sync_fs.read_bytes(path))~=

async fn read_lines(path: text) -> Result<[text], IoError>:
    """Read file lines (async via thread pool)."""
    spawn_blocking(\: sync_fs.read_lines(path))~=
```

### 7.2 Async Network IO Architecture

**Problem:** Network IO IS truly async on all platforms (epoll/kqueue/IOCP).

**Solution:**

```
Layer 1: Platform-specific async FFI (new rt_async_tcp_* functions)
Layer 2: Async wrapper (nogc_async_mut/net/)
Layer 3: Sync wrapper via block_on (nogc_sync_mut/net/ - for convenience)
```

```simple
# New FFI functions needed (Rust runtime additions)
extern fn rt_async_tcp_connect(addr: text, waker_id: i64) -> i64  # Returns handle
extern fn rt_async_tcp_read(handle: i64, size: usize, waker_id: i64) -> Poll<Result<[u8], i64>>
extern fn rt_async_tcp_write(handle: i64, data: [u8], waker_id: i64) -> Poll<Result<usize, i64>>
extern fn rt_async_tcp_accept(handle: i64, waker_id: i64) -> Poll<Result<i64, i64>>

# Event loop integration
extern fn rt_event_loop_poll(timeout_ms: i64) -> i64  # Number of ready events
extern fn rt_event_loop_register(handle: i64, interest: i64) -> bool
extern fn rt_event_loop_deregister(handle: i64) -> bool
```

```simple
# nogc_async_mut/net/tcp.spl

struct AsyncTcpStream:
    handle: i64

    static async fn connect(addr: text) -> Result<AsyncTcpStream, NetError>:
        val handle = rt_async_tcp_connect(addr, current_waker_id())
        if handle < 0: Err(NetError.ConnectionFailed(addr))
        else: Ok(AsyncTcpStream(handle: handle))

    async fn read(size: usize) -> Result<[u8], NetError>:
        loop:
            val result = rt_async_tcp_read(self.handle, size, current_waker_id())
            match result:
                case Poll.Ready(Ok(data)): return Ok(data)
                case Poll.Ready(Err(code)): return Err(NetError.from_code(code))
                case Poll.Pending: suspend~=  # Yield to scheduler

    async fn write(data: [u8]) -> Result<usize, NetError>:
        loop:
            val result = rt_async_tcp_write(self.handle, data, current_waker_id())
            match result:
                case Poll.Ready(Ok(n)): return Ok(n)
                case Poll.Ready(Err(code)): return Err(NetError.from_code(code))
                case Poll.Pending: suspend~=

    async fn close():
        rt_async_tcp_close(self.handle)
```

### 7.3 Sync Network (nogc_sync_mut)

```simple
# nogc_sync_mut/net/tcp.spl

struct TcpStream:
    handle: i64

    static fn connect(addr: text) -> Result<TcpStream, NetError>:
        val result = tcp_stream_connect(addr)
        match result:
            case Ok(stream): Ok(TcpStream(handle: stream))
            case Err(e): Err(NetError.from_error(e))

    fn read(size: usize) -> Result<[u8], NetError>:
        tcp_stream_read(self.handle, size)

    fn write(data: [u8]) -> Result<usize, NetError>:
        tcp_stream_write(self.handle, data)

    fn close():
        tcp_stream_close(self.handle)
```

### 7.4 API Comparison Table

| Operation | nogc_sync_mut | nogc_async_mut | User Change |
|-----------|--------------|----------------|-------------|
| `fs.read_text(path)` | `-> Result<text, IoError>` | `async -> Result<text, IoError>` | Add `~=` |
| `tcp.connect(addr)` | `-> Result<TcpStream, NetError>` | `async -> Result<AsyncTcpStream, NetError>` | Add `~=` |
| `tcp.read(stream, n)` | `-> Result<[u8], NetError>` | `async -> Result<[u8], NetError>` | Add `~=` |
| `http.get(url)` | `-> Result<Response, HttpError>` | `async -> Result<Response, HttpError>` | Add `~=` |

**Conversion:** Add `~=` after each IO call. That's it.

---

## 8) Rust Async Backend: Runtime FFI Additions

### 8.1 Required Rust Runtime Additions

From `doc/design/rust_to_simple_migration_plan.md`, the runtime crate must provide:

**Event Loop (using mio or tokio as backend):**
```rust
// New functions to add to runtime crate
#[no_mangle] pub extern "C" fn rt_event_loop_create() -> *mut EventLoop
#[no_mangle] pub extern "C" fn rt_event_loop_poll(loop: *mut EventLoop, timeout_ms: i64) -> i64
#[no_mangle] pub extern "C" fn rt_event_loop_register(loop: *mut EventLoop, fd: i64, interest: u32) -> bool
#[no_mangle] pub extern "C" fn rt_event_loop_deregister(loop: *mut EventLoop, fd: i64) -> bool
```

**Async TCP (wrapping tokio or mio):**
```rust
#[no_mangle] pub extern "C" fn rt_async_tcp_listen(addr: *const c_char) -> i64
#[no_mangle] pub extern "C" fn rt_async_tcp_accept(listener: i64) -> i64
#[no_mangle] pub extern "C" fn rt_async_tcp_connect(addr: *const c_char) -> i64
#[no_mangle] pub extern "C" fn rt_async_tcp_read(stream: i64, buf: *mut u8, len: usize) -> i64
#[no_mangle] pub extern "C" fn rt_async_tcp_write(stream: i64, buf: *const u8, len: usize) -> i64
```

**Thread Pool (for spawn_blocking):**
```rust
#[no_mangle] pub extern "C" fn rt_thread_pool_spawn(task_fn: extern "C" fn(*mut c_void), data: *mut c_void) -> i64
#[no_mangle] pub extern "C" fn rt_thread_pool_poll(task_id: i64) -> i32  // 0=pending, 1=ready, -1=error
#[no_mangle] pub extern "C" fn rt_thread_pool_result(task_id: i64) -> *mut c_void
```

### 8.2 Backend Selection

```sdn
# simple.sdn - Runtime backend configuration
runtime:
  async_backend: mio          # mio (lightweight) or tokio (full-featured)
  thread_pool_size: 4         # For spawn_blocking
  event_loop: epoll           # Auto-detected: epoll (linux), kqueue (macos), iocp (windows)
```

---

## 9) Test Directory Updates

### 9.1 New Test Structure

Mirror the lib variant structure:

```
test/
  unit/
    common/                          # Tests for common/ modules
      math_spec.spl
      json_spec.spl
      collections_spec.spl
      async_core_spec.spl
      ...
    nogc_sync_mut/                   # Tests for sync IO
      fs_spec.spl
      net_tcp_spec.spl
      net_udp_spec.spl
      http_client_spec.spl
      database_spec.spl
      ...
    nogc_async_mut/                  # Tests for async IO
      async_fs_spec.spl
      async_tcp_spec.spl
      async_udp_spec.spl
      async_http_spec.spl
      runtime_executor_spec.spl
      runtime_scheduler_spec.spl
      future_combinators_spec.spl
      ...
    nogc_async_mut_noalloc/          # Tests for baremetal
      embedded_runtime_spec.spl
      resource_pool_spec.spl
      semihost_io_spec.spl
      ...
    gc_async_mut/                    # Tests for GC variant
      gc_auto_close_spec.spl
      gc_finalizer_spec.spl
      pure_tensor_spec.spl
      ...
  feature/
    portability/                     # Cross-profile portability tests
      sync_to_async_spec.spl         # Same code works in both profiles
      nogc_to_gc_spec.spl            # Unique ptr code works with GC
    usage/
      # Existing feature tests, reorganized by profile
      async_file_io_spec.spl         # @profile=nogc_async_mut
      networking_spec.spl            # @profile=nogc_sync_mut
      ...
  integration/
    lib/
      # End-to-end tests across profiles
      thread_pool_async_spec.spl
      ...
```

### 9.2 Migration of Existing Tests

| Current Location | New Location | Profile |
|-----------------|-------------|---------|
| `test/unit/std/async_spec.spl` | `test/unit/nogc_async_mut/async_runtime_spec.spl` | nogc_async_mut |
| `test/unit/std/async_host_spec.spl` | `test/unit/nogc_async_mut/runtime_host_spec.spl` | nogc_async_mut |
| `test/unit/std/async_embedded_spec.spl` | `test/unit/nogc_async_mut_noalloc/runtime_embedded_spec.spl` | nogc_async_mut_noalloc |
| `test/unit/std/net_spec.spl` | `test/unit/nogc_sync_mut/net_spec.spl` | nogc_sync_mut |
| `test/feature/usage/async_file_io_spec.spl` | `test/feature/usage/async_file_io_spec.spl` (keep, add @profile) | nogc_async_mut |
| `test/feature/usage/networking_spec.spl` | `test/feature/usage/networking_spec.spl` (keep, add @profile) | nogc_sync_mut |

### 9.3 Profile-Aware Test Runner

```simple
# Test runner changes
# bin/simple test --profile=nogc_sync_mut      # Run tests for sync profile
# bin/simple test --profile=nogc_async_mut     # Run tests for async profile
# bin/simple test --profile=all                # Run all profiles
```

---

## 10) Implementation Phases

### Phase 0: Foundation (Prerequisite)

**Goal:** Get async/await actually working in the compiler.

1. Implement `SplFuture`, `SplPoll`, `SplTask` C structs in `runtime.h`
2. Wire type constants `TYPE_FUTURE=20`, `TYPE_POLL=21`, `TYPE_TASK=22` to runtime
3. Implement minimal `block_on()` executor in runtime
4. Unskip and fix at least 5 basic async tests
5. **Estimated effort:** 6-9 hours (from async_implementation_status.md)

### Phase 1: Create `common/` Variant

**Goal:** Extract pure-logic modules from flat `lib/` into `lib/common/`.

1. Create `lib/common/` directory structure
2. Move pure modules (math, json, collections, text, etc.) - ~60 modules
3. Move `async_core.spl` contents into `lib/common/async_core/`
4. Define shared error types in `lib/common/error/`
5. Update imports: `use std.math` -> resolves from `lib/common/math/`
6. Run all existing tests to verify nothing breaks
7. **File moves:** ~200 files
8. **Import changes:** ~150 files

### Phase 2: Create `nogc_sync_mut/` Variant

**Goal:** Extract IO modules into sync variant.

1. Create `lib/nogc_sync_mut/` directory structure
2. Move file IO modules (fs/, file_system/) with sync API
3. Move network modules (net/, tcp/, http/, etc.) with sync API
4. Move FFI bindings (ffi/) for sync operations
5. Move IO support modules (env/, cli/, shell/, etc.)
6. Define sync `Reader`/`Writer` traits
7. Update imports
8. Create tests in `test/unit/nogc_sync_mut/`
9. **File moves:** ~150 files
10. **New files:** ~20 (trait definitions, __init__ modules)

### Phase 3: Create `nogc_async_mut/` Variant

**Goal:** Build async wrappers around sync IO.

1. Create `lib/nogc_async_mut/` directory structure
2. Implement async fs/ wrapping sync via `spawn_blocking`
3. Implement async net/ with new async FFI functions
4. Move async runtime code (async/, async_host/) into `runtime/`
5. Implement `AsyncReader`/`AsyncWriter` traits
6. Add new Rust FFI functions for event loop + async TCP
7. Move existing async tests, unskip where possible
8. **New files:** ~40
9. **Rust runtime additions:** ~500 lines

### Phase 4: Create `nogc_async_mut_noalloc/` Variant

**Goal:** Baremetal async with static allocation.

1. Create `lib/nogc_async_mut_noalloc/` directory structure
2. Move baremetal/ modules
3. Move async_embedded runtime
4. Implement resource declarations (pool, queue, set, dict)
5. Implement compile-time verification passes (from baremetal_async_resources_v0.3.md)
6. Semihost IO async wrappers
7. **New files:** ~30
8. **Compiler additions:** ~1000 lines (resource verification)

### Phase 5: Create `gc_async_mut/` Variant

**Goal:** Default GC variant that re-exports nogc_async_mut with GC semantics.

1. Create `lib/gc_async_mut/` directory structure
2. Re-export async modules with GC pointer semantics
3. Move pure/ (ML), cuda/, torch/, gpu/ (require GC)
4. Add GC-specific utilities (auto_close, finalizer, weak_ref)
5. Make this the default profile
6. **New files:** ~20
7. **Moved files:** ~80 (ML/GPU modules)

### Phase 6: SDoctest Updates

**Goal:** Profile-aware documentation testing.

1. Add `@compiled` modifier to sdoctest extractor
2. Add `@profile=<name>` modifier
3. Update runner to pass `--lib-profile` flag
4. Update existing doc blocks with appropriate profile markers
5. **Changed files:** ~5 (sdoctest runner/extractor/types)

### Phase 7: Profile Selection & Compiler Integration

**Goal:** Compile-time profile resolution.

1. Add `lib_profile` to `simple.sdn` build config
2. Implement import resolution based on profile hierarchy
3. Add `--lib-profile` CLI flag
4. Add `@when(profile.X)` conditional compilation support
5. Update `bin/simple build` to respect profile
6. **Compiler changes:** ~500 lines

---

## 11) Open Questions

1. **Should `common/` modules have a separate namespace?** E.g., `use std.common.math` vs `use std.math` (resolved to common/ by hierarchy)
   - **Recommendation:** Keep `use std.math` - resolve by hierarchy. Less code change.

2. **Should sync and async types share the same name?** E.g., both called `TcpStream` or `TcpStream` vs `AsyncTcpStream`?
   - **Recommendation:** Same name within their profile. If you import from explicit profile, use `sync_net.TcpStream` vs `async_net.TcpStream`.

3. **How to handle modules that need BOTH sync and async?** E.g., database with sync queries but async streaming.
   - **Recommendation:** Put in the lowest variant needed. Database goes in `nogc_sync_mut/`, async DB goes in `nogc_async_mut/` as override.

4. **When to build the Rust runtime additions?** Phase 3 needs new FFI functions.
   - **Recommendation:** Phase 3 is blocked on Rust runtime work. Start Rust additions in parallel with Phase 2.

5. **Should the existing flat test/unit/std/ be preserved or fully migrated?**
   - **Recommendation:** Preserve during transition. Create new test dirs alongside, migrate incrementally. Delete old only when all tests pass in new locations.

---

## 12) Risk Assessment

| Risk | Impact | Mitigation |
|------|--------|------------|
| Massive file moves break imports | High | Phase each move with full test runs |
| Async runtime still not executable | Blocks Phase 3 | Phase 0 is prerequisite |
| Circular dependencies between variants | Medium | Strict hierarchy: child can only import parent |
| Profile resolution adds compile time | Low | Cache resolution, only re-resolve on config change |
| GC/nogc pointer difference causes subtle bugs | High | Comprehensive portability tests (Phase 5) |
| Existing 3690 sdoctest blocks break | Medium | Default profile = gc_async_mut (current behavior) |

---

## References

- `doc/plan/manual_memory_safety_plan.md` - Pointer type definitions
- `doc/design/baremetal_async_resources_v0.3.md` - Baremetal async resource system
- `doc/feature/async_implementation_status.md` - Current async state (70% infra, 0% executable)
- `doc/design/rust_to_simple_migration_plan.md` - Rust runtime FFI plan
- `doc/plan/src_refactor_lib_rename_2026-02-19.md` - Previous lib reorganization plan
- Rust: tokio, embassy, mio patterns
- TypeScript: Node.js fs/promises, AbortController, stream patterns
