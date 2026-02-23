# Async I/O Backend Library Comparison — All 4 Platforms

**Date:** 2026-02-23
**Purpose:** Evaluate C and Rust async I/O libraries for Simple's runtime backend across Linux, macOS, Windows, and FreeBSD.
**Related:** `doc/design/async_io_nginx_perf_optimization.md`

---

## Table of Contents

1. [OS-Level I/O Model Summary](#1-os-level-io-model-summary)
2. [C Libraries Comparison](#2-c-libraries-comparison)
3. [Rust Runtimes Comparison](#3-rust-runtimes-comparison)
4. [Reactor vs Proactor Analysis](#4-reactor-vs-proactor-analysis)
5. [Cross-Platform Zero-Copy](#5-cross-platform-zero-copy)
6. [Per-Platform File I/O Strategy](#6-per-platform-file-io-strategy)
7. [Architecture Options for Simple](#7-architecture-options-for-simple)
8. [Recommendation](#8-recommendation)

---

## 1. OS-Level I/O Model Summary

| OS | Network I/O API | Model | File I/O API | Model | Zero-Copy |
|----|----------------|-------|-------------|-------|-----------|
| **Linux 5.1+** | epoll / io_uring | Reactor / Proactor | io_uring | Proactor | sendfile, splice, SEND_ZC |
| **Linux <5.1** | epoll | Reactor | pread/pwrite (blocking) | N/A | sendfile, splice |
| **macOS** | kqueue | Reactor (hybrid) | dispatch_io / threadpool | N/A | sendfile (different API!) |
| **FreeBSD** | kqueue | Reactor (hybrid) | kqueue EVFILT_AIO | Hybrid | sendfile (Netflix-optimized) |
| **Windows** | IOCP | Proactor | IOCP | Proactor | TransmitFile, RIO |

**Key insight:** Linux (io_uring) and Windows (IOCP) are natively completion-based (proactor). macOS and FreeBSD are readiness-based (reactor) for network I/O, with varying file I/O support. A unified backend must bridge this gap.

---

## 2. C Libraries Comparison

### 2.1 Summary Matrix

| Library | Linux | macOS | Windows | FreeBSD | io_uring | Async File I/O | API Model | sendfile | License | Maintained | Vendorable |
|---------|-------|-------|---------|---------|----------|---------------|-----------|----------|---------|------------|------------|
| **libuv** | epoll, io_uring(opt-in) | kqueue | IOCP | kqueue | opt-in (v1.49+) | threadpool | callback/reactor | `uv_fs_sendfile()` | MIT | very active | moderate (~30K SLOC) |
| **libevent** | epoll | kqueue | IOCP/select | kqueue | no | none | callback/reactor | yes (evbuffer) | BSD-3 | stalled (4yr no stable) | hard |
| **libev** | epoll, io_uring | kqueue | **select only** | kqueue | partial | none | callback/reactor | no | BSD-2 | frozen | easy (~8K SLOC) |
| **liburing** | io_uring | -- | -- | -- | native | true async | completion/proactor | via SQE | LGPL+MIT | very active | good (~5K SLOC) |
| **libxev** | io_uring/epoll | kqueue | IOCP (WIP) | untested | native | via io_uring | completion/proactor | no | MIT | active | needs Zig |
| **picoev** | epoll | kqueue | -- | kqueue | no | none | callback/reactor | no | BSD-2 | dead | easy (~800 SLOC) |
| **libfiber** | epoll, io_uring | kqueue | IOCP | kqueue | yes | via syscall hooks | coroutine | no | LGPL-3 | active | moderate |
| **PhotonLibOS** | epoll, io_uring | kqueue | -- | -- | yes | via io_uring | C++ coroutine | ? | Apache-2 | very active | C++ only |

### 2.2 Detailed Analysis

#### libuv (Node.js foundation)

**Strengths:**
- True 4-platform support (the only C library with production IOCP)
- Battle-tested: powers Node.js, Julia, Neovim, uvloop
- `uv_fs_sendfile()` available
- MIT license, actively maintained
- io_uring support added in v1.45 (then made opt-in in v1.49 due to bugs)

**Weaknesses:**
- File I/O always uses threadpool (even on Linux), not io_uring by default
- io_uring reverted to opt-in: `UV_LOOP_USE_IO_URING_SQPOLL` flag required
- H2O HTTP server got **14-29% faster** after removing libuv (overhead from abstraction layer + threadpool synchronization)
- Not trivially vendorable (~30K SLOC, ~100 source files, CMake build)
- Callback-style API adds complexity

**Verdict:** Safe choice but leaves performance on the table. The 14-29% overhead vs raw syscalls is significant for a performance-focused runtime.

#### libev (Lightweight, embeddable)

**Strengths:**
- Tiny (~8K SLOC), compiles from single `ev.c`
- Has io_uring backend (`ev_iouring.c`)
- Very fast watcher manipulation (array + ring buffer of bit vectors)
- Scales ~2x better than libevent per fd count increase

**Weaknesses:**
- **Windows: select only (no IOCP)** — unusable for production Windows
- No file I/O abstraction
- No sendfile/splice
- Essentially frozen (single author, CVS)

**Verdict:** Excellent as a Unix-only event loop component but fails the 4-platform requirement.

#### liburing (Linux io_uring wrapper)

**Strengths:**
- Direct access to io_uring with all features (SQPOLL, registered buffers, multishot, SEND_ZC)
- Maintained by the io_uring kernel developer (Jens Axboe)
- Small (~5K SLOC), easy to vendor
- True async file I/O, network I/O, and everything else

**Weaknesses:**
- **Linux only** — not a cross-platform solution by itself

**Verdict:** Must-have for Linux. Combine with other backends for other platforms.

#### libxev (Zig, Ghostty's event loop)

**Strengths:**
- Completion-based (proactor) API on all platforms
- io_uring + epoll (runtime selectable) on Linux, kqueue on macOS
- Zero runtime allocations
- Used in production (Ghostty terminal, 1000+ daily users)

**Weaknesses:**
- **Requires Zig toolchain** to build (can pre-build `.a` + `.h`)
- Windows IOCP support still WIP
- FreeBSD not explicitly tested
- No sendfile support

**Verdict:** Architecturally closest to what we need, but the Zig dependency and WIP Windows support are blockers.

### 2.3 C Library Verdict

**No single C library covers all 4 platforms with maximum performance.** The best strategy is a thin abstraction layer over platform-specific backends:

| Platform | Best C Backend |
|----------|---------------|
| Linux | liburing (direct io_uring) |
| macOS | raw kqueue + dispatch_io |
| FreeBSD | raw kqueue + EVFILT_AIO |
| Windows | raw IOCP (+ TransmitFile) |

---

## 3. Rust Runtimes Comparison

### 3.1 Summary Matrix

| Runtime | Linux | macOS | Windows | FreeBSD | io_uring | Thread Model | File I/O | License | Maintained | C FFI |
|---------|-------|-------|---------|---------|----------|-------------|----------|---------|------------|-------|
| **tokio** | epoll | kqueue | IOCP (wepoll) | kqueue | no (separate tokio-uring, stalled) | work-stealing | threadpool (blocking) | MIT | very active | feasible but heavy |
| **monoio** | io_uring/epoll | kqueue | -- | -- | native (primary) | thread-per-core | true async (io_uring) | MIT/Apache-2 | active (ByteDance) | good for TPC model |
| **glommio** | io_uring only | -- | -- | -- | native (only) | thread-per-core | true async + Direct I/O | MIT/Apache-2 | alpha | Linux only |
| **mio** | epoll | kqueue | IOCP (wepoll) | kqueue | no | none (lib only) | none | MIT | active (tokio-rs) | excellent (tiny API) |
| **compio** | io_uring | polling | IOCP | polling | native | thread-per-core | true async (io_uring/IOCP) | MIT | active (Apache Iggy) | good |
| **smol** | epoll | kqueue | IOCP | kqueue | no | configurable | threadpool | MIT/Apache-2 | active | excellent (1K SLOC) |
| **polling** | epoll | kqueue | IOCP | kqueue | no | single-poller | none | MIT/Apache-2 | active (smol-rs) | excellent |
| **nuclei** | io_uring/epoll | kqueue | IOCP | ? | yes | runtime-agnostic | yes | MIT/Apache-2 | dormant | moderate |

### 3.2 Detailed Analysis

#### tokio

**Pros:** Dominant ecosystem (95% of async Rust crates target it), 4-platform, 58K+ stars
**Cons:** Work-stealing (bad for TPC model), file I/O is blocking-in-threadpool, io_uring not in mainline (tokio-uring stalled since 2022), heavy for FFI (43 crates), dynamic linking issues (#6927)
**Verdict:** Wrong architecture for a performance I/O runtime. Work-stealing is 3x slower at 16 cores.

#### monoio (ByteDance)

**Pros:** Thread-per-core (3x tokio at 16 cores), native io_uring, true async file I/O, gateway beat NGINX by 20%, RPC 26% faster than tokio, MIT license
**Cons:** No Windows support, `!Send` futures (thread-local only), smaller ecosystem
**Verdict:** Best performance but Linux+macOS only. If Windows is required, not viable alone.

#### compio

**Pros:** True completion-based I/O on all 3 major platforms (io_uring + IOCP + polling fallback), thread-per-core, Apache Iggy production validation (rewrote from tokio, better throughput + p99), MIT license
**Cons:** Smaller community, polling fallback on macOS/FreeBSD (not true async file I/O there), owned buffer requirement breaks tokio ecosystem compatibility
**Verdict:** Best cross-platform completion-based runtime. The Apache Iggy migration is strong production validation.

#### mio (Low-level)

**Pros:** Widest platform support, tiny API, zero allocations, no global state, used by tokio underneath
**Cons:** No file I/O, no io_uring, no timers, no scheduler — must build everything on top
**Verdict:** Good as the readiness notification layer if building a custom runtime.

#### smol + polling

**Pros:** Smallest (~1K SLOC), simplest embedding, widest platform support, 15% less memory than tokio, MIT license
**Cons:** No io_uring, file I/O via threadpool, not completion-based
**Verdict:** Best for "just works everywhere" baseline but misses io_uring performance.

### 3.3 Rust Runtime Verdict

| Use Case | Best Rust Runtime |
|----------|------------------|
| Max Linux performance | **monoio** |
| Cross-platform completion-based | **compio** |
| Simplest FFI integration | **smol** or **mio** |
| Widest platform support | **polling** (event notification only) |

---

## 4. Reactor vs Proactor Analysis

### 4.1 Definitions

**Reactor (readiness):** OS tells you "fd is ready" → you do the I/O syscall
- 2-step: wait → do I/O
- Buffer allocated after notification
- epoll, kqueue

**Proactor (completion):** You submit I/O operation → OS does it → OS tells you "done"
- 1-step: submit, get result
- Buffer allocated before submission (must remain valid until completion)
- io_uring, IOCP

### 4.2 The Critical File I/O Problem

**Regular files are always "ready" in epoll/kqueue.** This means:
- epoll: file reads block the thread even though epoll says "ready"
- kqueue EVFILT_READ on regular files: same problem

This forces reactor-based runtimes (tokio, smol, libuv) to use **threadpool** for file I/O. Only proactor-based runtimes (io_uring, IOCP) can do true async file I/O.

### 4.3 Emulation Overhead

**Proactor-on-reactor (completion API on epoll/kqueue):**
- One extra syscall per operation (epoll_wait + read vs just io_uring submit)
- Buffer allocated upfront but unused until readiness (wasted memory for idle connections)
- No DMA-to-user-buffer optimization possible
- For network I/O: overhead dwarfed by network latency (practical impact <5%)
- For file I/O: impossible to emulate without threadpool

**Reactor-on-proactor (readiness API on IOCP/io_uring):**
- Wasteful: extra kernel round-trip per logical read
- io_uring has `IORING_OP_POLL_ADD` for readiness mode (rarely used)
- Better to just use proactor natively

### 4.4 Recommendation

**Expose a completion-based (proactor) API.** This is the forward-looking model:
- Matches io_uring (Linux) and IOCP (Windows) natively
- Emulatable on epoll/kqueue with small overhead
- Industry direction: compio, TigerBeetle, Boost.Asio all chose this
- Handles both network and file I/O uniformly

---

## 5. Cross-Platform Zero-Copy

### 5.1 sendfile Variants

```c
// Linux
ssize_t sendfile(int out_fd, int in_fd, off_t *offset, size_t count);
// Returns bytes written; out_fd was socket-only pre-2.6.33
// Max 0x7ffff000 bytes per call
// Internally uses splice() since kernel 2.6.23

// macOS  (DIFFERENT SIGNATURE!)
int sendfile(int fd, int s, off_t offset, off_t *len, struct sf_hdtr *hdtr, int flags);
// Returns 0 on success; *len is in/out (bytes actually sent)
// Supports headers/trailers via sf_hdtr
// Known issue: may buffer data until socket close in some configs

// FreeBSD (YET ANOTHER SIGNATURE!)
int sendfile(int fd, int s, off_t offset, size_t nbytes,
             struct sf_hdtr *hdtr, off_t *sbytes, int flags);
// Separate nbytes (requested) and *sbytes (actual)
// SF_NODISKIO flag: returns EBUSY instead of blocking
// Netflix contributed major optimizations

// Windows
BOOL TransmitFile(SOCKET hSocket, HANDLE hFile, DWORD nNumberOfBytesToWrite,
                  DWORD nNumberOfBytesPerSend, LPOVERLAPPED lpOverlapped,
                  LPTRANSMIT_FILE_BUFFERS lpTransmitBuffers, DWORD dwFlags);
// Integrates with IOCP via OVERLAPPED
// Supports headers/trailers via TRANSMIT_FILE_BUFFERS
```

### 5.2 Additional Zero-Copy Paths

| Technique | Linux | macOS | FreeBSD | Windows |
|-----------|-------|-------|---------|---------|
| sendfile | `sendfile(2)` | `sendfile(2)` (different!) | `sendfile(2)` (different!) | `TransmitFile` |
| splice | `splice(2)` | -- | -- | -- |
| io_uring SEND_ZC | kernel 6.0+ | -- | -- | -- |
| io_uring registered buffers | kernel 5.1+ | -- | -- | -- |
| RIO (Registered I/O) | -- | -- | -- | Windows 8+ |
| Kernel TLS + sendfile | kernel 4.13+ | -- | -- | -- |

### 5.3 Performance Data

| Technique | Metric | Value |
|-----------|--------|-------|
| sendfile CPU savings | Netflix CDN | 15% → 2% CPU |
| sendfile throughput | vs read+write | +8-19% |
| sendfile syscalls | vs read+write | 1 vs 2 (2x fewer) |
| sendfile context switches | vs read+write | 2 vs 4 (2x fewer) |
| io_uring SEND_ZC | crossover point | >3000 byte packets (kernel 6.10) |
| io_uring SEND_ZC | peak throughput | 50 GiB/s per node (400 Gb/s NIC) |
| Windows RIO | vs IOCP | 33% throughput, 6x fewer ctx switches |

---

## 6. Per-Platform File I/O Strategy

### 6.1 Linux (kernel 5.1+)

**Best: io_uring**
- True async read/write/fsync/openat/close/statx
- Registered buffers for DMA-capable zero-copy
- Batch submissions: one `io_uring_enter()` per event loop tick
- SQPOLL mode: zero syscalls for hot paths
- Random 4KiB read: 1.7M IOPS (polled), 2.8x libaio
- PostgreSQL 18: 2-3x faster seq scans, 35-40% NVMe throughput gain

**Fallback (kernel <5.1): threadpool + pread/pwrite**

### 6.2 macOS

**Best: dispatch_io (Grand Central Dispatch)**
- Apple's recommended async file I/O
- Thread pool managed by GCD (constrained to CPU count)
- Integrates with kqueue-based dispatch sources
- Not truly async at kernel level (uses blocking reads on worker threads)

**Alternative: threadpool + pread/pwrite**
- Simpler, portable
- Same practical performance (dispatch_io does this internally)

**Note:** macOS does NOT support kqueue EVFILT_AIO. POSIX AIO only supports signal-based notification on macOS, not kqueue integration.

### 6.3 FreeBSD

**Best: kqueue EVFILT_AIO**
- True integration of POSIX AIO with kqueue event loop
- Set `aio_sigevent.sigev_notify = SIGEV_KEVENT`
- Set `aio_sigevent.sigev_notify_kqueue = kq_fd`
- Submit via `aio_read()` / `aio_write()`
- kqueue delivers completion event
- Netflix contributed major sendfile optimizations to FreeBSD

### 6.4 Windows

**Best: IOCP**
- Native async file I/O via `ReadFileEx` / `WriteFileEx` with `OVERLAPPED`
- Or `ReadFile` / `WriteFile` with `OVERLAPPED` + completion port
- Completion notifications via `GetQueuedCompletionStatusEx()` (batched dequeue)
- TransmitFile for zero-copy file→socket
- RIO for high-throughput datagram scenarios (33% better than IOCP, 6x fewer ctx switches)

### 6.5 Summary

| Platform | Network | File I/O | Zero-Copy | Notes |
|----------|---------|----------|-----------|-------|
| Linux 5.1+ | io_uring (or epoll fallback) | io_uring | sendfile, splice, SEND_ZC | Best platform for async I/O |
| Linux <5.1 | epoll | threadpool | sendfile, splice | Rare in 2026 |
| macOS | kqueue | dispatch_io or threadpool | sendfile (quirky API) | No kernel-level async file I/O |
| FreeBSD | kqueue | EVFILT_AIO | sendfile (Netflix-optimized) | Surprisingly good file I/O |
| Windows | IOCP | IOCP | TransmitFile, RIO | Fully async, both network + file |

---

## 7. Architecture Options for Simple

### Option A: Pure C — Thin Abstraction Over Raw Syscalls

```
┌────────────────────────────────────────┐
│       Simple Async I/O API             │
│  (completion-based, .spl interfaces)   │
└──────────────┬─────────────────────────┘
               │ extern fn rt_*
┌──────────────▼─────────────────────────┐
│    Platform Abstraction Layer (C)      │
│    src/runtime/platform/async_*.h      │
├──────────┬──────────┬─────────┬────────┤
│  Linux   │  macOS   │ FreeBSD │ Windows│
│ liburing │ kqueue + │ kqueue +│ IOCP + │
│ (vendor) │ dispatch │ AIO     │ Transmit│
│          │          │         │ File   │
└──────────┴──────────┴─────────┴────────┘
```

**Pros:**
- Zero FFI overhead (C runtime is already C)
- Full control over every syscall
- Smallest binary size
- No external toolchain dependencies (Zig, Rust)
- Vendor only liburing (~5K SLOC) for Linux; rest is raw syscalls

**Cons:**
- Most implementation work (write kqueue/IOCP/dispatch_io wrappers ourselves)
- Must handle all edge cases per platform
- Harder to maintain cross-platform correctness
- No Rust safety guarantees

**Estimated work:** ~3K-5K SLOC of C platform code

### Option B: Rust Runtime via C FFI (compio or monoio)

```
┌────────────────────────────────────────┐
│       Simple Async I/O API             │
│  (completion-based, .spl interfaces)   │
└──────────────┬─────────────────────────┘
               │ extern fn rt_*
┌──────────────▼─────────────────────────┐
│    C Shim Layer (~500 SLOC)            │
│    src/runtime/async_ffi.c             │
└──────────────┬─────────────────────────┘
               │ dlopen / static link
┌──────────────▼─────────────────────────┐
│    Rust cdylib / staticlib             │
│    src/runtime/rust_async/             │
│    (compio or monoio + FFI exports)    │
└────────────────────────────────────────┘
```

**Pros:**
- Leverages battle-tested async code
- Rust safety for complex event loop logic
- compio gives true completion I/O on all 3 major platforms
- Less platform-specific edge case work

**Cons:**
- Rust toolchain required for build (already have Cargo.toml for runtime)
- FFI boundary cost per call (~1-2ns, negligible for I/O)
- Buffer ownership transfer across FFI adds complexity
- Binary size increase (~200KB-1MB for async runtime)
- `block_on` at FFI boundary blocks C thread (need callback-based API for true async)

**Estimated work:** ~1K-2K SLOC of Rust + ~500 SLOC C shim

### Option C: Hybrid — C for Hot Path, Rust for Complex Logic

```
┌────────────────────────────────────────┐
│       Simple Async I/O API             │
│  (completion-based, .spl interfaces)   │
└──────────────┬─────────────────────────┘
               │ extern fn rt_*
┌──────────────▼─────────────────────────┐
│  C Hot Path (sendfile, writev, epoll)  │
│  + liburing (Linux, vendored)          │
│  src/runtime/platform/async_*.h        │
├──────────────┬─────────────────────────┤
│ Optional Rust│  For: io_uring advanced │
│ cdylib       │  features, IOCP, complex│
│              │  scheduling logic       │
└──────────────┴─────────────────────────┘
```

**Pros:**
- Hot path (sendfile, writev, basic epoll) is pure C — zero overhead
- Complex logic (io_uring multishot, IOCP completion ports, scheduling) in Rust
- Can ship without Rust (degraded mode: epoll + threadpool)
- Incremental: start with pure C, add Rust backends later

**Cons:**
- Two codebases to maintain
- Build system complexity

### Option D: libuv as Cross-Platform Base + liburing Override

```
┌────────────────────────────────────────┐
│       Simple Async I/O API             │
│  (completion-based, .spl interfaces)   │
└──────────────┬─────────────────────────┘
               │ extern fn rt_*
┌──────────────▼─────────────────────────┐
│  Abstraction Layer                     │
├────────────────────┬───────────────────┤
│  Linux: liburing   │  Other: libuv     │
│  (bypass libuv)    │  (macOS, Win, BSD)│
└────────────────────┴───────────────────┘
```

**Pros:**
- libuv handles macOS/Windows/FreeBSD complexity (proven correct)
- liburing gives max Linux performance
- Both are C, no Rust dependency
- libuv is the most battle-tested cross-platform I/O library

**Cons:**
- libuv adds 14-29% overhead on non-Linux platforms
- Two very different backends to maintain
- libuv is ~30K SLOC to vendor (or link dynamically)
- libuv's threadpool file I/O is suboptimal on macOS/FreeBSD

---

## 8. Recommendation

### Primary: Option A (Pure C) — with liburing for Linux

**Rationale:**

1. **Simple already has a C runtime** (`src/runtime/`). Adding more C is natural.
2. **liburing is only ~5K SLOC** and gives full io_uring access. Trivially vendorable.
3. **Raw kqueue/IOCP are well-documented** and the code for each platform is ~500-1000 SLOC.
4. **Zero FFI overhead** — no Rust boundary crossing for hot-path I/O.
5. **No new toolchain dependencies** — the project already builds with clang.
6. **The Rust runtime already has `Cargo.toml`** (`src/runtime/Cargo.toml`) for future Rust integration, but making the async I/O core depend on Rust adds build complexity for all platforms.
7. **compio is the Rust alternative** if Rust is preferred. It has the right model (completion-based, thread-per-core, io_uring + IOCP + polling), production validation (Apache Iggy), and MIT license. But it adds ~200KB binary size and requires Rust toolchain.

### Implementation Plan

#### Layer 1: Platform Event Driver (C)

New file per platform in `src/runtime/platform/`:

```c
// src/runtime/platform/async_driver.h — unified interface

typedef struct spl_driver spl_driver;
typedef struct spl_completion {
    int64_t id;        // user-supplied operation ID
    int64_t result;    // bytes transferred or negative errno
    int64_t flags;
} spl_completion;

// Lifecycle
spl_driver* spl_driver_create(int queue_depth);
void spl_driver_destroy(spl_driver* d);

// Submit operations (returns operation ID)
int64_t spl_driver_submit_read(spl_driver* d, int64_t fd, void* buf, int64_t len, int64_t offset);
int64_t spl_driver_submit_write(spl_driver* d, int64_t fd, const void* buf, int64_t len, int64_t offset);
int64_t spl_driver_submit_accept(spl_driver* d, int64_t listen_fd);
int64_t spl_driver_submit_connect(spl_driver* d, int64_t fd, const char* addr, int port);
int64_t spl_driver_submit_recv(spl_driver* d, int64_t fd, void* buf, int64_t len);
int64_t spl_driver_submit_send(spl_driver* d, int64_t fd, const void* buf, int64_t len);
int64_t spl_driver_submit_close(spl_driver* d, int64_t fd);
int64_t spl_driver_submit_sendfile(spl_driver* d, int64_t out_fd, int64_t in_fd, int64_t offset, int64_t len);

// Batch submit all queued operations
int64_t spl_driver_flush(spl_driver* d);

// Wait for completions
int64_t spl_driver_poll(spl_driver* d, spl_completion* out, int64_t max, int64_t timeout_ms);

// Cancel a pending operation
bool spl_driver_cancel(spl_driver* d, int64_t op_id);
```

#### Layer 2: Per-Platform Backends

| File | Platform | Backend | LOC Estimate |
|------|----------|---------|-------------|
| `async_linux_uring.c` | Linux 5.1+ | liburing (vendored) | ~800 |
| `async_linux_epoll.c` | Linux <5.1 | epoll + threadpool | ~600 |
| `async_macos.c` | macOS | kqueue + dispatch_io | ~700 |
| `async_freebsd.c` | FreeBSD | kqueue + EVFILT_AIO | ~600 |
| `async_windows.c` | Windows | IOCP + TransmitFile | ~900 |
| `async_driver.h` | All | Unified interface | ~100 |
| **Total new C** | | | **~3700** |

#### Layer 3: Additional Syscall Wrappers

Add to existing `unix_common.h` / `platform_win.h`:

```c
// sendfile (per-platform variants)
int64_t rt_sendfile(int64_t out_fd, int64_t in_fd, int64_t offset, int64_t count);

// Vectored I/O
int64_t rt_writev(int64_t fd, const char** bufs, const int64_t* lens, int64_t count);
int64_t rt_readv(int64_t fd, int64_t* sizes, int64_t count, char*** out_bufs);

// Socket options
int64_t rt_socket_set_reuseport(int64_t fd, bool enabled);
int64_t rt_socket_set_cork(int64_t fd, bool enabled);
int64_t rt_socket_set_keepalive(int64_t fd, bool enabled, int64_t idle_secs);

// CPU affinity (Linux/FreeBSD)
bool rt_thread_set_affinity(int64_t cpu_id);
```

#### Layer 4: Simple API (.spl)

```simple
# src/lib/nogc_async_mut/io/driver.spl — wraps C driver

class IoDriver:
    handle: i64  # opaque pointer to spl_driver

    static fn new() -> IoDriver
    static fn with_depth(depth: i64) -> IoDriver

    fn submit_read(fd: i64, buf: [u8], offset: i64) -> OpId
    fn submit_write(fd: i64, data: [u8], offset: i64) -> OpId
    fn submit_accept(listen_fd: i64) -> OpId
    fn submit_connect(fd: i64, addr: text, port: i64) -> OpId
    fn submit_recv(fd: i64, buf: [u8]) -> OpId
    fn submit_send(fd: i64, data: [u8]) -> OpId
    fn submit_close(fd: i64) -> OpId
    fn submit_sendfile(out_fd: i64, in_fd: i64, offset: i64, len: i64) -> OpId

    fn flush() -> i64
    fn poll(max: i64, timeout_ms: i64) -> [Completion]
    fn cancel(op: OpId) -> bool

    me close()

struct Completion:
    id: OpId
    result: i64
    flags: i64

type OpId = i64
```

### Fallback Strategy

```
compile-time detection:
  if linux && kernel >= 5.1:
    use async_linux_uring.c
  elif linux:
    use async_linux_epoll.c
  elif macos:
    use async_macos.c
  elif freebsd:
    use async_freebsd.c
  elif windows:
    use async_windows.c

runtime fallback (Linux):
  if io_uring_setup() fails:
    fall back to epoll + threadpool
```

### Future: Rust Integration Path

If Rust is desired later (for io_uring advanced features, IOCP complexity, or safety):

1. The `spl_driver` interface (`async_driver.h`) stays identical
2. Replace individual platform `.c` files with a Rust `cdylib` implementing the same C API
3. **compio** is the recommended Rust runtime for this (completion-based, thread-per-core, 3-platform)
4. The `src/runtime/Cargo.toml` already exists for this purpose

---

## Appendix: Source References

### C Libraries
- libuv: github.com/libuv/libuv, docs.libuv.org
- libuv io_uring: phoronix.com/news/libuv-io-uring
- libuv overhead: blog.kazuhooku.com/2014/09/the-reasons-why-i-stopped-using-libuv
- libev: software.schmorp.de/pkg/libev, libev.schmorp.de/bench.html
- libevent: github.com/libevent/libevent
- liburing: github.com/axboe/liburing, kernel.dk/io_uring.pdf
- libxev: github.com/mitchellh/libxev
- libfiber: github.com/iqiyi/libfiber
- PhotonLibOS: github.com/alibaba/PhotonLibOS
- TigerBeetle I/O: tigerbeetle.com/blog/2022-11-23-a-friendly-abstraction-over-iouring-and-kqueue

### Rust Runtimes
- tokio: tokio.rs, github.com/tokio-rs/tokio
- monoio: github.com/bytedance/monoio
- glommio: github.com/DataDog/glommio
- mio: github.com/tokio-rs/mio
- compio: github.com/compio-rs/compio, compio.rs/docs
- smol: github.com/smol-rs/smol
- polling: github.com/smol-rs/polling
- Apache Iggy compio migration: iggy.apache.org/blogs/2025/11/17/websocket-io-uring

### Architecture
- Reactor vs Proactor: boost.org/doc/libs/1_86_0/doc/html/boost_asio/overview/core/async.html
- io_uring vs epoll: alibabacloud.com/blog/io-uring-vs--epoll
- io_uring SEND_ZC: kernel-recipes.org/en/2024/schedule/efficient-zero-copy-networking-using-io_uring
- Windows IOCP: learn.microsoft.com/en-us/windows/win32/fileio/i-o-completion-ports
- Windows RIO: serverframework.com/asynchronousevents/2012/08/winsock-registered-io
- FreeBSD AIO: man.freebsd.org/cgi/man.cgi?query=aio&sektion=4
- macOS dispatch_io: developer.apple.com/documentation/dispatch/dispatchio
- sendfile variants: man7.org/linux/man-pages/man2/sendfile.2.html
- Netflix sendfile: netflixtechblog.com/serving-100-gbps
- PostgreSQL 18 io_uring: pganalyze.com/blog/postgres-18-async-io
