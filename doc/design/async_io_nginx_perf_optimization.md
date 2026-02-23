# Async I/O Performance Optimization — NGINX-Class Throughput

**Status:** PLAN
**Date:** 2026-02-23
**Goal:** Optimize Simple's async I/O (file / console / network) to achieve NGINX-class throughput on common workloads (static files, reverse-proxy forwarding, JSON endpoints).
**Research:** `doc/research/async_io_backend_comparison_2026-02-23.md` — full C/Rust library comparison

---

## Table of Contents

1. [Current State Assessment](#1-current-state-assessment)
2. [Competition Baseline](#2-competition-baseline)
3. [Performance Targets](#3-performance-targets)
4. [Architecture Decisions](#4-architecture-decisions)
5. [Unified Completion Driver (C)](#5-unified-completion-driver-c)
6. [Interface Changes (Simple)](#6-interface-changes-simple)
7. [Runtime C Layer Changes](#7-runtime-c-layer-changes)
8. [Milestone Plan](#8-milestone-plan)
9. [Benchmark Matrix](#9-benchmark-matrix)

---

## 1. Current State Assessment

### What Simple Has Today

| Component | Location | Architecture | Status |
|-----------|----------|-------------|--------|
| Event Loop | `nogc_async_mut/io/event_loop.spl` | epoll/kqueue abstraction | Working |
| Async TCP | `nogc_async_mut/io/tcp.spl` | Event loop driven | Working |
| Async UDP | `nogc_async_mut/io/udp.spl` | Event loop driven | Working |
| Async File | `nogc_async_mut/io/file.spl` | Epoll (limited on macOS) | Partial |
| Host Runtime | `nogc_async_mut/async_host/` | Work-stealing, multi-threaded | Working |
| Embedded Runtime | `nogc_async_mut/async_embedded.spl` | Fixed-capacity, baremetal | Working |
| HTTP Server | `nogc_sync_mut/http_server/` | **Sync only** (blocking) | Working |
| HTTP Client | `nogc_sync_mut/http_client/` | **Sync only** (blocking) | Working |
| Concurrency | `nogc_async_mut/concurrent/` | Channels, mutex, rwlock | Working |
| Actor Model | `nogc_async_mut/gen_*.spl` | Erlang-style (mailbox, monitors) | Working |

### What the C Runtime Has

Platform headers in `src/runtime/platform/` provide:

- **File ops:** pread/pwrite, mmap/munmap/madvise/msync, flock
- **Process ops:** fork/execvp, waitpid, signals
- **Timing:** clock_gettime (monotonic), gettimeofday
- **DLL:** dlopen/dlsym/dlclose

### Critical Gaps

| Feature | Status | Impact |
|---------|--------|--------|
| sendfile/splice | Not implemented | No zero-copy file→socket |
| io_uring | Not implemented | No async file I/O on Linux |
| writev/readv | Not implemented | No scatter-gather writes |
| Async HTTP | Not implemented | HTTP server is blocking |
| picohttpparser | Not integrated | Slow HTTP parsing |
| SO_REUSEPORT | Not used | No multi-worker socket sharing |
| TCP_CORK/TCP_NOPUSH | Not used | No write coalescing |
| Worker process model | Not implemented | Single-process only |
| Console backpressure | Not implemented | Logging can stall hot path |

### Current Architecture Diagram

```
                    ┌──────────────────┐
                    │  Simple User Code │
                    └──────┬───────────┘
                           │ await
                    ┌──────▼───────────┐
                    │   HostRuntime    │
                    │ (work-stealing)  │
                    │ N worker threads │
                    └──────┬───────────┘
                           │ poll()
                    ┌──────▼───────────┐
                    │   EventLoop      │
                    │ (single global)  │
                    └──────┬───────────┘
                           │
              ┌────────────┼────────────┐
              │            │            │
        ┌─────▼─────┐ ┌───▼────┐ ┌────▼─────┐
        │  epoll    │ │ kqueue │ │  (IOCP)  │
        │  Linux    │ │ macOS  │ │ Windows  │
        └───────────┘ └────────┘ └──────────┘
```

**Problem:** Single global event loop is a bottleneck. Work-stealing scheduler adds cross-core contention. No zero-copy paths. HTTP is sync-only.

---

## 2. Competition Baseline

### NGINX Performance Numbers (2024-2025 data)

**Hardware:** Dual Xeon E5-2699 v3 (36 cores), 2x 40 GbE

| Metric | NGINX Number | Notes |
|--------|-------------|-------|
| Hello-world RPS (36 cores) | **3,298,511** | 0-byte HTTP response |
| Hello-world RPS (1 core) | 145,551 | Linear scaling baseline |
| 1 KB RPS (36 cores) | 1,309,358 | Small payload |
| Reverse proxy p99 | **<8 ms** | At 85K RPS, HTTPS TLSv1.3 |
| Static file throughput | **72 Gbps** | Large files, NIC-saturated |
| HTTPS RPS (36 cores) | 2,175,945 | TLS overhead ~34% |

### TechEmpower Round 23 (March 2025)

**Hardware:** Xeon Gold 6330 (56 cores), 40 Gbps NIC

| Framework | Plaintext RPS | Notes |
|-----------|--------------|-------|
| may-minihttp (Rust) | ~7,000,000 | Network-saturated |
| ntex (Rust) | ~7,000,000 | Network-saturated |
| H2O (C) | ~7,000,000 | Network-saturated |
| drogon (C++) | ~6,500,000 | |
| Fiber (Go) | ~735,000 | JSON test |

### Key Architectural Choices That Make NGINX Fast

1. **Fixed N workers (= CPU cores)** — no per-connection threads
2. **Event-driven non-blocking I/O** — epoll/kqueue per worker
3. **sendfile for static files** — zero-copy kernel path
4. **Worker process model** — no cross-thread locking
5. **Connection reuse** — keep-alive default on

---

## 3. Performance Targets

### Must Hit (Milestone Gate)

| Domain | Metric | Target | Comparison |
|--------|--------|--------|------------|
| **Network** | Hello-world RPS (1 core) | >100K | NGINX: 145K |
| **Network** | Hello-world RPS (N cores) | >80% linear scaling | NGINX: ~91K/core |
| **Network** | Sustained connections | >100K (C100K) | NGINX: easily |
| **Network** | p99 latency under load | <10 ms at 50K RPS | NGINX: <8 ms |
| **File** | Static file throughput | >10 Gbps (NIC permitting) | NGINX: 72 Gbps |
| **File** | Syscalls per static file serve | ≤3 (open, sendfile, close) | vs 5 (open, read, write, ...) |
| **Console** | Log impact on hot path | <5% throughput drop | vs no logging |

### Should Hit (Competitive)

| Domain | Metric | Target |
|--------|--------|--------|
| Network | JSON endpoint RPS | >500K (4 cores) |
| File | io_uring random read IOPS | >500K (4 KiB) |
| Network | HTTP parse throughput | >5M req/s (picohttpparser AVX2) |

### Could Hit (Stretch)

| Domain | Metric | Target |
|--------|--------|--------|
| Network | TechEmpower top-50 plaintext | >2M RPS |
| Network | Thread-per-core 16-core scaling | >90% efficiency |

---

## 4. Architecture Decisions

### Decision 1: Worker Model — **Thread-per-Core** (not work-stealing)

**Rationale:** Monoio benchmarks show thread-per-core is **3x faster at 16 cores** than work-stealing (Tokio). NGINX uses the same model (worker processes, not threads).

**Change from current:** The existing `HostScheduler` with work-stealing stays as a **general-purpose** runtime. A new `ServerRuntime` uses thread-per-core for I/O-bound server workloads.

```
Current:                           New:
┌────────────────────┐            ┌────────────────────┐
│   HostRuntime      │            │   ServerRuntime     │
│ (work-stealing)    │            │ (thread-per-core)   │
│ shared global loop │            │ per-worker loop     │
└────────────────────┘            │ per-worker arena    │
                                  │ SO_REUSEPORT        │
                                  └────────────────────┘
```

**Must:** Per-worker event loop, per-worker memory arena, SO_REUSEPORT.
**Should:** CPU pinning (sched_setaffinity).
**Could:** NUMA-aware allocation.

### Decision 2: I/O Backend — **Pure C, Per-Platform Optimal**

**Research outcome:** No single C or Rust library covers all 4 platforms at max performance. libuv adds 14-29% overhead. The best strategy is a thin C abstraction (`spl_driver`) over platform-native APIs.

| Domain | Linux 5.1+ | Linux <5.1 | macOS | FreeBSD | Windows |
|--------|-----------|-----------|-------|---------|---------|
| **Network** | io_uring (primary), epoll (fallback) | epoll | kqueue | kqueue | IOCP |
| **File (async)** | io_uring | threadpool + pread | dispatch_io or threadpool | kqueue EVFILT_AIO | IOCP |
| **File (zero-copy)** | sendfile, splice, SEND_ZC | sendfile, splice | sendfile (different API!) | sendfile (Netflix-optimized) | TransmitFile |
| **Console** | buffered async writer | buffered async writer | buffered async writer | buffered async writer | buffered async writer |

**Per-platform backend file:**

| File | Platform | Backend | LOC Est. |
|------|----------|---------|----------|
| `async_linux_uring.c` | Linux 5.1+ | liburing (vendored, ~5K SLOC) | ~800 |
| `async_linux_epoll.c` | Linux <5.1 | epoll + threadpool | ~600 |
| `async_macos.c` | macOS | kqueue + dispatch_io | ~700 |
| `async_freebsd.c` | FreeBSD | kqueue + EVFILT_AIO | ~600 |
| `async_windows.c` | Windows | IOCP + TransmitFile | ~900 |
| `async_driver.h` | All | Unified completion interface | ~100 |

**Rationale:**
- io_uring networking: **+25% throughput** when batched (ping-pong), but **-50-67%** for streaming. Use io_uring as primary on Linux (HTTP is ping-pong), epoll as runtime fallback.
- io_uring file I/O: **2.8x libaio** for random reads (1.7M IOPS polled). PostgreSQL 18 saw 2-3x seq scan improvement.
- sendfile: **CPU 15% → 2%** (Netflix), **+8-19% throughput**, 2x fewer syscalls.
- macOS file I/O: kqueue EVFILT_READ on regular files is useless (always "ready"). Must use dispatch_io or threadpool. macOS does NOT support kqueue EVFILT_AIO (FreeBSD does).
- FreeBSD: kqueue EVFILT_AIO integrates POSIX AIO into the event loop — true async file I/O without threadpool.
- Windows IOCP: natively completion-based for both network and file I/O. TransmitFile for zero-copy. RIO for high-throughput UDP (33% better, 6x fewer ctx switches).

**Libraries evaluated and rejected:**
- **libuv:** 14-29% overhead (H2O measurement), threadpool for all file I/O, io_uring support reverted to opt-in
- **libevent:** Stalled (4yr no stable release), no io_uring
- **libev:** No Windows IOCP (select only), no file I/O
- **libxev:** Requires Zig toolchain, Windows IOCP still WIP
- **tokio (Rust):** Work-stealing (3x slower at 16 cores), file I/O blocking-in-threadpool, no mainline io_uring
- **compio (Rust):** Strong candidate if Rust FFI is acceptable. Production-validated (Apache Iggy). Reserved as future upgrade path.

**Future Rust upgrade path:** The `spl_driver` C interface can be reimplemented in Rust (compio) without changing the Simple API. `src/runtime/Cargo.toml` already exists.

### Decision 3: HTTP Parser — **picohttpparser via SFFI**

**Rationale:** picohttpparser with AVX2 does **7M parses/s**. Zero-allocation, stateless, zero-copy (returns slices into read buffer). Used by H2O, proven in production.

**Alternative considered:** llhttp (Node.js) — 2x faster than old http-parser but still allocates. picohttpparser is better for our zero-copy pipeline.

### Decision 4: No libuv — **Direct Syscalls**

**Rationale:** H2O removed libuv and got **14-29% faster**. Simple already has its own event loop abstraction. libuv adds indirection we don't need. libev lacks IOCP. libevent is stalled. The platform code is ~3700 SLOC total — manageable.

### Decision 5: HTTP Server — **New Async Module**

The current sync HTTP server (`nogc_sync_mut/http_server/`) stays for simple use cases. A new high-performance async HTTP server goes in `nogc_async_mut/http_server/`.

### Decision 6: Completion-Based (Proactor) API — **Not Reactor**

**Rationale:** Research shows the industry is moving to completion-based I/O. Boost.Asio, compio, TigerBeetle, and io_uring all use this model.

| Aspect | Reactor (readiness) | Proactor (completion) | Winner |
|--------|--------------------|-----------------------|--------|
| Native on Linux | epoll | io_uring | Proactor (io_uring is future) |
| Native on Windows | — | IOCP | Proactor |
| File I/O | Impossible (files always "ready") | Native | **Proactor** |
| Buffer ownership | Deferred (allocate on demand) | Upfront (for duration) | Reactor (less memory) |
| Emulation cost | — | ~1 extra syscall on epoll/kqueue | Acceptable |
| Unified model | Cannot handle files | Handles network + file | **Proactor** |

**The critical finding:** Regular files are always "ready" in epoll/kqueue (EVFILT_READ returns immediately). This forces reactor runtimes to use threadpool for file I/O. Only proactor (io_uring, IOCP) can do true async file I/O. A completion-based API is strictly more capable.

**Emulation on reactor platforms (macOS kqueue, FreeBSD kqueue, Linux epoll fallback):**
1. User submits `driver.submit_read(fd, buf, len)`
2. Driver registers fd with epoll/kqueue for EPOLLIN/EVFILT_READ
3. On readiness, driver performs `read(fd, buf, len)` internally
4. Driver posts completion to user (as if it were io_uring/IOCP)

Overhead: one extra syscall per operation. Negligible for network I/O (dwarfed by network latency). For file I/O on macOS/FreeBSD, use dispatch_io/EVFILT_AIO respectively (not epoll/kqueue readiness).

### Decision 7: sendfile API Differences — **Per-Platform Wrapper**

Each OS has a different sendfile signature:

```c
// Linux:   ssize_t sendfile(int out_fd, int in_fd, off_t *offset, size_t count);
// macOS:   int sendfile(int fd, int s, off_t offset, off_t *len, struct sf_hdtr *hdtr, int flags);
// FreeBSD: int sendfile(int fd, int s, off_t offset, size_t nbytes, struct sf_hdtr *hdtr, off_t *sbytes, int flags);
// Windows: BOOL TransmitFile(SOCKET, HANDLE, DWORD, DWORD, LPOVERLAPPED, LPTRANSMIT_FILE_BUFFERS, DWORD);
```

The `spl_driver_submit_sendfile()` function in `async_driver.h` abstracts all variants behind a single interface.

---

## 5. Unified Completion Driver (C)

This is the core abstraction — a single C API that all 5 platform backends implement. Simple's `.spl` code calls `extern fn` wrappers around this API.

### 5.1 Driver Interface (`src/runtime/platform/async_driver.h`)

```c
#pragma once
#include <stdint.h>
#include <stdbool.h>

/* Opaque driver handle — contains platform-specific state */
typedef struct spl_driver spl_driver;

/* Completion result — returned from spl_driver_poll() */
typedef struct spl_completion {
    int64_t id;        /* user-supplied operation ID from submit_* */
    int64_t result;    /* bytes transferred (>=0) or negative errno */
    int64_t flags;     /* platform-specific flags */
} spl_completion;

/* ── Lifecycle ── */
spl_driver* spl_driver_create(int64_t queue_depth);
void        spl_driver_destroy(spl_driver* d);

/* ── Submit operations (queued, not executed until flush) ── */
/* All return an operation ID (>0) or negative errno */

/* Network */
int64_t spl_driver_submit_accept(spl_driver* d, int64_t listen_fd);
int64_t spl_driver_submit_connect(spl_driver* d, int64_t fd, const char* addr, int64_t port);
int64_t spl_driver_submit_recv(spl_driver* d, int64_t fd, void* buf, int64_t len);
int64_t spl_driver_submit_send(spl_driver* d, int64_t fd, const void* buf, int64_t len);
int64_t spl_driver_submit_sendfile(spl_driver* d, int64_t sock_fd, int64_t file_fd,
                                    int64_t offset, int64_t len);
int64_t spl_driver_submit_writev(spl_driver* d, int64_t fd,
                                  const void** bufs, const int64_t* lens, int64_t count);

/* File */
int64_t spl_driver_submit_read(spl_driver* d, int64_t fd, void* buf, int64_t len, int64_t offset);
int64_t spl_driver_submit_write(spl_driver* d, int64_t fd, const void* buf, int64_t len, int64_t offset);
int64_t spl_driver_submit_open(spl_driver* d, const char* path, int64_t flags, int64_t mode);
int64_t spl_driver_submit_close(spl_driver* d, int64_t fd);
int64_t spl_driver_submit_fsync(spl_driver* d, int64_t fd);

/* Timers */
int64_t spl_driver_submit_timeout(spl_driver* d, int64_t timeout_ms);

/* ── Batch control ── */
int64_t spl_driver_flush(spl_driver* d);   /* submit all queued ops to kernel */

/* ── Wait for completions ── */
int64_t spl_driver_poll(spl_driver* d, spl_completion* out, int64_t max, int64_t timeout_ms);
/* Returns number of completions filled (0..max), or negative errno */

/* ── Cancel a pending operation ── */
bool spl_driver_cancel(spl_driver* d, int64_t op_id);

/* ── Query ── */
const char* spl_driver_backend_name(spl_driver* d);  /* "io_uring", "epoll", "kqueue", "iocp" */
bool        spl_driver_supports_sendfile(spl_driver* d);
bool        spl_driver_supports_zero_copy(spl_driver* d);
```

### 5.2 Platform Backend Implementations

#### Linux io_uring (`async_linux_uring.c`)

```c
#include "async_driver.h"
#include <liburing.h>   /* vendored in src/runtime/vendor/liburing/ */

struct spl_driver {
    struct io_uring ring;
    int64_t next_id;
};

spl_driver* spl_driver_create(int64_t queue_depth) {
    spl_driver* d = calloc(1, sizeof(spl_driver));
    io_uring_queue_init(queue_depth, &d->ring, 0);
    d->next_id = 1;
    return d;
}

int64_t spl_driver_submit_recv(spl_driver* d, int64_t fd, void* buf, int64_t len) {
    struct io_uring_sqe* sqe = io_uring_get_sqe(&d->ring);
    io_uring_prep_recv(sqe, fd, buf, len, 0);
    int64_t id = d->next_id++;
    io_uring_sqe_set_data64(sqe, id);
    return id;
}

int64_t spl_driver_submit_sendfile(spl_driver* d, int64_t sock_fd, int64_t file_fd,
                                    int64_t offset, int64_t len) {
    /* io_uring: use splice(file_fd -> pipe -> sock_fd) or SEND_ZC */
    struct io_uring_sqe* sqe = io_uring_get_sqe(&d->ring);
    io_uring_prep_splice(sqe, file_fd, offset, sock_fd, -1, len, SPLICE_F_MOVE);
    int64_t id = d->next_id++;
    io_uring_sqe_set_data64(sqe, id);
    return id;
}

int64_t spl_driver_flush(spl_driver* d) {
    return io_uring_submit(&d->ring);
}

int64_t spl_driver_poll(spl_driver* d, spl_completion* out, int64_t max, int64_t timeout_ms) {
    struct io_uring_cqe* cqe;
    int count = 0;
    /* wait for at least 1 */
    io_uring_wait_cqe_timeout(&d->ring, &cqe, &(struct __kernel_timespec){
        .tv_sec = timeout_ms / 1000, .tv_nsec = (timeout_ms % 1000) * 1000000
    });
    /* drain all available */
    unsigned head;
    io_uring_for_each_cqe(&d->ring, head, cqe) {
        if (count >= max) break;
        out[count].id = io_uring_cqe_get_data64(cqe);
        out[count].result = cqe->res;
        out[count].flags = cqe->flags;
        count++;
    }
    io_uring_cq_advance(&d->ring, count);
    return count;
}
```

#### Linux epoll fallback (`async_linux_epoll.c`)

Emulates completion API on readiness:
1. `submit_recv()` → stores (fd, buf, len) in pending map, registers EPOLLIN
2. `flush()` → no-op (epoll_ctl already done)
3. `poll()` → `epoll_wait()`, then for each ready fd: perform `read(fd, buf, len)`, post completion

File I/O: dispatched to threadpool (N = CPU count).

#### macOS kqueue (`async_macos.c`)

Network: same emulation pattern as epoll fallback (readiness → internal read → completion).
File I/O: `dispatch_io_read()` / `dispatch_io_write()` via GCD, completion posted when done.
sendfile: macOS `sendfile()` (note different arg order and `off_t *len` in/out parameter).

#### FreeBSD kqueue (`async_freebsd.c`)

Network: same emulation pattern as macOS.
File I/O: `aio_read()` / `aio_write()` with `sigev_notify = SIGEV_KEVENT` → kqueue delivers EVFILT_AIO completion. True kernel-async without threadpool.
sendfile: FreeBSD `sendfile()` with `SF_NODISKIO` flag, Netflix-optimized.

#### Windows IOCP (`async_windows.c`)

All operations natively completion-based:
1. `submit_recv()` → `WSARecv()` with `OVERLAPPED`
2. `submit_read()` → `ReadFile()` with `OVERLAPPED`
3. `submit_sendfile()` → `TransmitFile()` with `OVERLAPPED`
4. `flush()` → no-op (operations submitted immediately on Windows)
5. `poll()` → `GetQueuedCompletionStatusEx()` (batch dequeue, ~65 completions/call average)

### 5.3 Runtime Detection and Fallback

```c
spl_driver* spl_driver_create(int64_t queue_depth) {
#if defined(__linux__)
    /* Try io_uring first */
    spl_driver* d = spl_driver_create_uring(queue_depth);
    if (d) return d;
    /* Fallback to epoll */
    return spl_driver_create_epoll(queue_depth);
#elif defined(__APPLE__)
    return spl_driver_create_kqueue_macos(queue_depth);
#elif defined(__FreeBSD__)
    return spl_driver_create_kqueue_freebsd(queue_depth);
#elif defined(_WIN32)
    return spl_driver_create_iocp(queue_depth);
#else
    #error "Unsupported platform"
#endif
}
```

### 5.4 Buffer Ownership Model

Completion-based I/O requires buffers to remain valid for the entire operation duration:

```
submit_recv(fd, buf, 4096)  →  buf must stay alive
         ... kernel doing I/O ...
poll() returns completion   →  buf now contains data, ownership returns to caller
```

For the proactor-on-reactor emulation (epoll/kqueue), buffers are technically unused until readiness, but we allocate upfront for API consistency.

**Per-worker arena allocator** provides fast buffer allocation:
- Bump-allocate buffers for incoming requests
- Reset arena after processing each batch of completions
- No malloc/free in the hot path

---

## 6. Interface Changes (Simple)

### 6.1 New: ServerRuntime (Thread-Per-Core)

```simple
# src/lib/nogc_async_mut/server_runtime/runtime.spl

class ServerRuntime:
    workers: [ServerWorker]
    num_workers: usize

    ## Create a server runtime with one worker per CPU core.
    static fn new() -> ServerRuntime

    ## Create with explicit worker count.
    static fn with_workers(count: usize) -> ServerRuntime

    ## Run the server event loop. Blocks until shutdown.
    fn run(handler: fn(WorkerContext))

    ## Graceful shutdown (finish in-flight, stop accepting).
    me shutdown()

class ServerWorker:
    id: usize
    loop: EventLoop          # Per-worker event loop (NOT shared)
    arena: BumpAllocator     # Per-worker memory arena

class WorkerContext:
    worker_id: usize
    loop: EventLoop
    arena: BumpAllocator

    fn spawn(task: Future<()>)
```

### 5.2 New: AsyncHttpServer

```simple
# src/lib/nogc_async_mut/http_server/server.spl

class AsyncHttpServer:
    runtime: ServerRuntime
    routes: [Route]

    static fn new() -> AsyncHttpServer
    static fn with_workers(count: usize) -> AsyncHttpServer

    ## Register a route handler.
    me route(method: HttpMethod, path: text, handler: fn(Request, Response))

    ## Serve static files from a directory.
    ## Uses sendfile zero-copy when possible.
    me static_files(prefix: text, dir: text)

    ## Start listening. Blocks until shutdown.
    fn listen(addr: text) -> Result<(), IoError>

    me shutdown()

class Request:
    method: HttpMethod
    path: text              # Slice into read buffer (zero-copy)
    headers: HeaderMap      # Fixed-size map, lazy parse uncommon
    body: [u8]              # Slice into read buffer
    query: text             # Slice

class Response:
    me status(code: i64) -> Response
    me header(key: text, value: text) -> Response
    me body(data: [u8]) -> Result<(), IoError>
    me body_text(s: text) -> Result<(), IoError>
    me send_file(path: text) -> Result<(), IoError>  # sendfile fast path
    me json(data: text) -> Result<(), IoError>

class HeaderMap:
    # Fixed array for common headers (Host, Content-Type, Content-Length, etc.)
    # Overflow to dynamic list for uncommon headers
    fn get(key: text) -> text?
    fn set(key: text, value: text)
```

### 5.3 Changed: EventLoop — Per-Worker Support

```simple
# src/lib/nogc_async_mut/io/event_loop.spl  (MODIFIED)

class EventLoop:
    epoll_fd: i64
    wakers: [WakerEntry]

    ## NEW: Create an event loop bound to the current thread.
    ## Each ServerWorker gets its own.
    static fn new_per_thread() -> EventLoop

    ## Existing: register/deregister/modify/poll (unchanged)
    fn register(fd: i64, interest: Interest, waker: Waker) -> Result
    fn deregister(fd: i64) -> Result
    fn poll(timeout_ms: i64) -> Result<[IoEvent]>

    ## NEW: Poll with batched event processing.
    fn poll_batch(timeout_ms: i64, max_events: i64) -> Result<[IoEvent]>
```

### 5.4 New: Zero-Copy File I/O

```simple
# src/lib/nogc_async_mut/io/sendfile.spl  (NEW)

## Send file contents directly to socket (zero-copy kernel path).
## Falls back to buffered read+write if sendfile unavailable.
fn sendfile(socket_fd: i64, file_fd: i64, offset: i64, count: i64) -> Result<i64, IoError>

## Vectored write (writev) — gather multiple buffers into one syscall.
fn writev(fd: i64, buffers: [[u8]]) -> Result<i64, IoError>

## Vectored read (readv) — scatter read into multiple buffers.
fn readv(fd: i64, sizes: [i64]) -> Result<[[u8]], IoError>
```

### 5.5 New: io_uring File Backend (Linux)

```simple
# src/lib/nogc_async_mut/io/uring.spl  (NEW, Linux only)

class IoUring:
    ring_fd: i64
    sq_size: i64
    cq_size: i64

    static fn new(queue_depth: i64) -> Result<IoUring, IoError>

    ## Submit a batch of I/O operations.
    fn submit() -> Result<i64, IoError>

    ## Wait for completions.
    fn wait(min_complete: i64, timeout_ms: i64) -> Result<[Completion], IoError>

    ## Queue operations (batched, submitted together).
    me queue_read(fd: i64, buf: [u8], offset: i64) -> SubmissionId
    me queue_write(fd: i64, data: [u8], offset: i64) -> SubmissionId
    me queue_readv(fd: i64, buffers: [[u8]], offset: i64) -> SubmissionId
    me queue_writev(fd: i64, buffers: [[u8]], offset: i64) -> SubmissionId

struct Completion:
    id: SubmissionId
    result: i64       # bytes transferred or negative errno
    flags: i64

type SubmissionId = i64
```

### 5.6 New: Async Logger

```simple
# src/lib/nogc_async_mut/logging/async_logger.spl  (NEW)

class AsyncLogger:
    queue: MpscQueue<LogEntry>
    flush_interval_ms: i64
    drop_policy: DropPolicy

    static fn new() -> AsyncLogger
    static fn with_config(flush_ms: i64, policy: DropPolicy) -> AsyncLogger

    ## Non-blocking log call — enqueues and returns immediately.
    fn log(level: LogLevel, msg: text)
    fn debug(msg: text)
    fn info(msg: text)
    fn warn(msg: text)
    fn error(msg: text)

    ## Start the background logger thread.
    fn start()

    ## Flush and stop.
    me shutdown()

enum DropPolicy:
    DropDebug     # Drop debug/trace when queue full
    DropAll       # Drop all when queue full
    Block         # Block caller when queue full (never for hot path)

enum LogLevel:
    Trace
    Debug
    Info
    Warn
    Error
```

### 6.7 New: IoDriver (Simple wrapper for spl_driver)

```simple
# src/lib/nogc_async_mut/io/driver.spl  (NEW — wraps C spl_driver)

class IoDriver:
    handle: i64  # opaque pointer to spl_driver*

    ## Create a driver with platform-optimal backend.
    ## Linux 5.1+: io_uring. Linux <5.1: epoll. macOS: kqueue. FreeBSD: kqueue+AIO. Windows: IOCP.
    static fn new() -> IoDriver
    static fn with_depth(depth: i64) -> IoDriver

    ## Submit operations (queued until flush).
    fn submit_accept(listen_fd: i64) -> OpId
    fn submit_connect(fd: i64, addr: text, port: i64) -> OpId
    fn submit_recv(fd: i64, buf: [u8]) -> OpId
    fn submit_send(fd: i64, data: [u8]) -> OpId
    fn submit_sendfile(sock_fd: i64, file_fd: i64, offset: i64, len: i64) -> OpId
    fn submit_writev(fd: i64, buffers: [[u8]]) -> OpId
    fn submit_read(fd: i64, buf: [u8], offset: i64) -> OpId
    fn submit_write(fd: i64, data: [u8], offset: i64) -> OpId
    fn submit_open(path: text, flags: i64, mode: i64) -> OpId
    fn submit_close(fd: i64) -> OpId
    fn submit_fsync(fd: i64) -> OpId
    fn submit_timeout(timeout_ms: i64) -> OpId

    ## Flush all queued operations to the kernel.
    fn flush() -> i64

    ## Wait for completions. Returns list of completed operations.
    fn poll(max: i64, timeout_ms: i64) -> [Completion]

    ## Cancel a pending operation.
    fn cancel(op: OpId) -> bool

    ## Query backend capabilities.
    fn backend_name() -> text
    fn supports_sendfile() -> bool
    fn supports_zero_copy() -> bool

    me close()

struct Completion:
    id: OpId
    result: i64    # bytes transferred (>=0) or negative errno
    flags: i64

type OpId = i64
```

### 6.8 Existing Interfaces — No Breaking Changes

The following interfaces are **unchanged**:

- `AsyncTcpListener`, `AsyncTcpStream` — same API, internal optimization only
- `AsyncRead`, `AsyncWrite`, `AsyncSeek`, `AsyncClose` traits — stable
- `HostRuntime` — still available for general-purpose async (not I/O-hot-path)
- Sync HTTP server — stays in `nogc_sync_mut/http_server/`
- All FFI functions — additive only (new `rt_*` functions, no removals)

---

## 7. Runtime C Layer Changes

### 6.1 New Functions in `unix_common.h`

```c
/* sendfile — zero-copy file-to-socket transfer */
int64_t rt_sendfile(int64_t out_fd, int64_t in_fd, int64_t offset, int64_t count);

/* splice — zero-copy fd-to-fd transfer (Linux only) */
int64_t rt_splice(int64_t fd_in, int64_t fd_out, int64_t len, int64_t flags);

/* writev — scatter-gather write */
int64_t rt_writev(int64_t fd, const char** bufs, const int64_t* lens, int64_t count);

/* readv — scatter-gather read */
int64_t rt_readv(int64_t fd, int64_t* sizes, int64_t count, char*** out_bufs);

/* Socket options for high-perf servers */
int64_t rt_socket_set_reuseport(int64_t fd, bool enabled);
int64_t rt_socket_set_cork(int64_t fd, bool enabled);       /* TCP_CORK (Linux) / TCP_NOPUSH (BSD) */
int64_t rt_socket_set_keepalive(int64_t fd, bool enabled, int64_t idle_secs);

/* CPU affinity (Linux) */
bool rt_thread_set_affinity(int64_t cpu_id);
int64_t rt_thread_get_cpu();
```

### 6.2 New File: `platform_linux_uring.h`

```c
/* io_uring ring creation/teardown */
int64_t rt_uring_setup(int64_t queue_depth, int64_t flags);
void rt_uring_teardown(int64_t ring_fd);

/* SQE submission */
int64_t rt_uring_queue_read(int64_t ring_fd, int64_t fd, void* buf, int64_t size, int64_t offset);
int64_t rt_uring_queue_write(int64_t ring_fd, int64_t fd, const void* buf, int64_t size, int64_t offset);
int64_t rt_uring_queue_readv(int64_t ring_fd, int64_t fd, struct iovec* iovs, int64_t count, int64_t offset);
int64_t rt_uring_queue_writev(int64_t ring_fd, int64_t fd, struct iovec* iovs, int64_t count, int64_t offset);
int64_t rt_uring_submit(int64_t ring_fd);

/* CQE collection */
int64_t rt_uring_wait(int64_t ring_fd, int64_t min_complete, int64_t timeout_ms,
                       int64_t* ids_out, int64_t* results_out, int64_t max_out);

/* Registered buffers (advanced — optional) */
int64_t rt_uring_register_buffers(int64_t ring_fd, void** bufs, int64_t* sizes, int64_t count);
void rt_uring_unregister_buffers(int64_t ring_fd);
```

### 6.3 New File: `platform_win_transmit.h`

```c
/* TransmitFile — Windows zero-copy equivalent of sendfile */
int64_t rt_transmit_file(int64_t socket, int64_t file_handle, int64_t count);
```

### 6.4 picohttpparser Integration

```c
/* Thin wrapper around picohttpparser */
/* src/runtime/http_parse.h */

struct rt_http_request {
    const char* method;     int method_len;
    const char* path;       int path_len;
    int minor_version;
    struct {
        const char* name;   int name_len;
        const char* value;  int value_len;
    } headers[64];
    int num_headers;
};

/* Parse HTTP/1.1 request from buffer. Returns bytes consumed or -1/-2 */
int64_t rt_http_parse_request(const char* buf, int64_t len, struct rt_http_request* req);
```

**Build:** Vendor `picohttpparser.c` + `picohttpparser.h` into `src/runtime/vendor/`. Compile with `-mavx2` when available, fallback to SSE4.2.

---

## 8. Milestone Plan

### Milestone 0 — Unified Completion Driver (C Layer)

**Files to create:**
- NEW: `src/runtime/platform/async_driver.h` — unified interface (~100 SLOC)
- NEW: `src/runtime/platform/async_linux_uring.c` — io_uring backend (~800 SLOC)
- NEW: `src/runtime/platform/async_linux_epoll.c` — epoll fallback (~600 SLOC)
- NEW: `src/runtime/platform/async_macos.c` — kqueue + dispatch_io (~700 SLOC)
- NEW: `src/runtime/platform/async_freebsd.c` — kqueue + EVFILT_AIO (~600 SLOC)
- NEW: `src/runtime/platform/async_windows.c` — IOCP + TransmitFile (~900 SLOC)
- NEW: `src/runtime/vendor/liburing/` — vendored liburing headers + source (~5K SLOC)
- NEW: `src/lib/nogc_async_mut/io/driver.spl` — Simple wrapper

**Deliverables:**
- Completion-based C API working on all 4 platforms
- Runtime auto-detection (io_uring → epoll fallback on Linux)
- sendfile abstraction across all 4 platform variants
- Simple IoDriver class wrapping the C API

**Success criteria:**
- Echo benchmark: same throughput as current epoll-based EventLoop (no regression)
- File read benchmark: io_uring path measurably faster than pread on Linux
- All platform backends compile and pass basic smoke tests
- `driver.backend_name()` correctly reports "io_uring", "epoll", "kqueue", or "iocp"

**Benchmark command:**
```bash
# Echo test via raw driver (no HTTP)
bin/simple run examples/driver_echo.spl
wrk -t4 -c100 -d10s http://localhost:9000/
# File read test
bin/simple run examples/driver_file_bench.spl --file=/tmp/test/1mb.bin --iodepth=32
```

### Milestone 1 — Thread-Per-Core Runtime + Net Loop (depends on M0)

**Files to create/modify:**
- NEW: `src/lib/nogc_async_mut/server_runtime/runtime.spl`
- NEW: `src/lib/nogc_async_mut/server_runtime/worker.spl`
- NEW: `src/lib/nogc_async_mut/server_runtime/arena.spl`
- MOD: `src/lib/nogc_async_mut/io/event_loop.spl` — per-thread support, use IoDriver
- MOD: `src/runtime/platform/unix_common.h` — add `rt_socket_set_reuseport`, `rt_thread_set_affinity`

**Deliverables:**
- Per-worker event loops (no sharing)
- SO_REUSEPORT socket distribution
- Per-worker bump allocator for request buffers
- Echo server benchmark

**Success criteria:**
- Stable at 100K keep-alive connections without memory blowup
- Near-linear RPS scaling from 1→4→8 cores
- p99 latency <5 ms under sustained load

**Benchmark command:**
```bash
# Server: bin/simple run examples/echo_server.spl --workers=4
# Client:
wrk -t4 -c100 -d30s http://localhost:8080/
wrk -t4 -c1000 -d30s http://localhost:8080/
wrk -t4 -c10000 -d30s http://localhost:8080/
```

### Milestone 2 — HTTP/1.1 Server Fast Path

**Files to create/modify:**
- NEW: `src/runtime/vendor/picohttpparser.c` + `.h`
- NEW: `src/runtime/http_parse.h` — wrapper
- NEW: `src/lib/nogc_async_mut/http_server/server.spl`
- NEW: `src/lib/nogc_async_mut/http_server/parser.spl` — SFFI wrapper
- NEW: `src/lib/nogc_async_mut/http_server/response.spl`
- NEW: `src/lib/nogc_async_mut/http_server/router.spl`
- NEW: `src/lib/nogc_async_mut/http_server/types.spl`
- MOD: `src/runtime/platform/unix_common.h` — add `rt_writev`, `rt_socket_set_cork`

**Deliverables:**
- picohttpparser integration (zero-copy parse → slices into read buffer)
- writev response (headers + body in one syscall)
- Keep-alive default on, pipelining (basic FIFO)
- Backpressure: cap per-connection outbound buffer

**Success criteria:**
- Hello-world RPS >100K (1 core), >400K (4 cores)
- Within 2x of NGINX on same hardware
- HTTP/1.1 compliance (keep-alive, chunked, pipelining)

**Benchmark command:**
```bash
# Server: bin/simple run examples/http_hello.spl --workers=4
wrk -t4 -c100 -d30s http://localhost:8080/
hey -n 100000 -c 200 http://localhost:8080/
# Compare: nginx -c examples/nginx_hello.conf
```

### Milestone 3 — Static File Server (sendfile)

**Files to create/modify:**
- MOD: `src/runtime/platform/unix_common.h` — add `rt_sendfile`
- NEW: `src/runtime/platform/platform_win_transmit.h` — add `rt_transmit_file`
- NEW: `src/lib/nogc_async_mut/io/sendfile.spl`
- MOD: `src/lib/nogc_async_mut/http_server/response.spl` — `send_file()` method
- MOD: `src/lib/nogc_async_mut/http_server/server.spl` — `static_files()` method

**Deliverables:**
- sendfile path for file → socket (Linux sendfile, BSD sendfile, Windows TransmitFile)
- Fallback to buffered read+write (for TLS, compression, etc.)
- fd caching for hot files (LRU, configurable size)
- writev for headers + small files in one syscall

**Success criteria:**
- Large file (1 MB+) throughput: NIC-saturated or >10 Gbps
- Syscalls per request: ≤3 (open/sendfile/close) for cached fd case
- Close to NGINX for cache-hit static files

**Benchmark command:**
```bash
# Create test files: dd if=/dev/urandom of=/tmp/test/1mb.bin bs=1M count=1
# Server: bin/simple run examples/static_server.spl --dir=/tmp/test --workers=4
wrk -t4 -c100 -d30s http://localhost:8080/1mb.bin
# Compare: nginx serving same directory
# Measure: perf stat -e syscalls:sys_enter_* -p <pid>
```

### Milestone 4 — io_uring Advanced Features (Linux)

**Depends on:** M0 (driver already has basic io_uring). This milestone adds advanced features.

**Files to create/modify:**
- MOD: `src/runtime/platform/async_linux_uring.c` — add registered buffers, SQPOLL, multishot
- NEW: `src/lib/nogc_async_mut/io/uring_advanced.spl` — advanced io_uring features
- MOD: `src/lib/nogc_async_mut/io/file.spl` — use IoDriver for async file ops

**Deliverables:**
- Registered buffers (`IORING_REGISTER_BUFFERS`) for DMA-capable zero-copy
- SQPOLL mode for zero-syscall submission on hot paths
- Multishot accept (single SQE handles all incoming connections)
- Multishot recv (6-8% QPS improvement for small messages)
- io_uring SEND_ZC (zero-copy send, kernel 6.0+, crossover >3KB packets)

**Success criteria:**
- Random 4 KiB read IOPS >500K
- Improved throughput for cache-miss workloads vs pread
- No regression for cache-hit workloads

**Benchmark command:**
```bash
# fio baseline: fio --name=randread --ioengine=io_uring --bs=4k --numjobs=4 --iodepth=128 --rw=randread --size=1G
# Simple: bin/simple run examples/uring_bench.spl --threads=4 --iodepth=128
```

### Milestone 5 — Async Logger

**Files to create/modify:**
- NEW: `src/lib/nogc_async_mut/logging/async_logger.spl`
- NEW: `src/lib/nogc_async_mut/logging/mpsc_queue.spl` — lock-free MPSC
- MOD: Integration with ServerRuntime

**Deliverables:**
- Lock-free MPSC queue (per worker → logger thread)
- Batched writes (flush every N messages or X ms)
- Drop policy (drop-debug under pressure, keep-error)
- Optional io_uring file write for log output

**Success criteria:**
- Enabling debug logs causes <5% throughput drop on HTTP server
- No log message loss for error/warn level
- Flush latency <10 ms

### Milestone 6 — LLVM Perf Pass

**Files to modify:**
- MOD: `src/compiler/70.backend/backend/mir_to_llvm.spl` — coroutine layout
- MOD: Build system — PGO + ThinLTO flags

**Deliverables:**
- Coroutine frames as plain structs (no hidden heap allocs)
- PGO build pipeline (instrument → wrk load → rebuild)
- ThinLTO for cross-module inlining
- @hot/@cold annotations in MIR

**Success criteria:**
- Measurable CPU/request reduction (>10%)
- p99 improvement from PGO
- No regression in compile times >2x

---

## 9. Benchmark Matrix

### Tools

| Tool | Purpose | Install |
|------|---------|---------|
| `wrk` | HTTP load generator (high throughput) | `apt install wrk` |
| `hey` | HTTP load generator (latency focused) | `go install github.com/rakyll/hey@latest` |
| `perf` | CPU profiling, syscall counting | Built-in Linux |
| `flamegraph` | Visualization of perf data | `cargo install flamegraph` |
| `fio` | Disk I/O benchmark (io_uring baseline) | `apt install fio` |
| `iperf3` | Network throughput baseline | `apt install iperf3` |
| `strace -c` | Syscall count summary | Built-in Linux |

### Benchmark Commands

```bash
# --- Baseline: measure hardware limits ---
iperf3 -s                           # Server
iperf3 -c localhost -t 30           # Client: max network throughput

# --- HTTP Hello-World ---
wrk -t$(nproc) -c100 -d30s http://localhost:8080/
wrk -t$(nproc) -c1000 -d30s http://localhost:8080/
wrk -t$(nproc) -c10000 -d30s http://localhost:8080/
hey -n 100000 -c 200 http://localhost:8080/    # Latency distribution

# --- Static File Serving ---
wrk -t$(nproc) -c100 -d30s http://localhost:8080/1kb.bin
wrk -t$(nproc) -c100 -d30s http://localhost:8080/1mb.bin
wrk -t$(nproc) -c100 -d30s http://localhost:8080/10mb.bin

# --- Syscall Analysis ---
strace -c -p <server_pid> -e trace=network,file -f   # Count syscalls
perf stat -e 'syscalls:sys_enter_sendfile*' -p <pid>  # sendfile usage

# --- CPU Profiling ---
perf record -g -p <server_pid> -- sleep 30
perf script | flamegraph > flame.svg

# --- io_uring File I/O ---
fio --name=baseline --ioengine=io_uring --bs=4k --numjobs=4 --iodepth=128 --rw=randread --size=1G
# Then compare with Simple's io_uring backend

# --- Connection Scaling ---
wrk -t4 -c100 -d30s http://localhost:8080/      # Low
wrk -t4 -c1000 -d30s http://localhost:8080/     # Medium
wrk -t4 -c10000 -d30s http://localhost:8080/    # High (C10K)
wrk -t4 -c100000 -d30s http://localhost:8080/   # C100K
```

### Comparison Matrix Template

Run each benchmark against both Simple and NGINX on identical hardware. Record:

```
| Test              | Workers | Conns  | Simple RPS | NGINX RPS | Ratio | Simple p99 | NGINX p99 |
|-------------------|---------|--------|-----------|-----------|-------|------------|-----------|
| hello-world       | 1       | 100    |           |           |       |            |           |
| hello-world       | 4       | 1000   |           |           |       |            |           |
| hello-world       | 8       | 10000  |           |           |       |            |           |
| json-200B         | 4       | 1000   |           |           |       |            |           |
| static-1KB        | 4       | 1000   |           |           |       |            |           |
| static-1MB        | 4       | 100    |           |           |       |            |           |
| static-10MB       | 4       | 100    |           |           |       |            |           |
| C10K sustained    | 4       | 10000  |           |           |       |            |           |
| C100K sustained   | 8       | 100000 |           |           |       |            |           |
```

### Perf Counters to Track

```bash
perf stat -e cycles,instructions,cache-references,cache-misses,\
            context-switches,cpu-migrations,page-faults \
         -p <pid> -- sleep 30
```

Key metrics:
- **IPC** (instructions per cycle) — should be >2.0 for optimized code
- **Cache miss rate** — <5% for hot path
- **Context switches/sec** — should be low (thread-per-core avoids this)
- **Syscalls/request** — minimize (target: 2-3 for hello-world, 3 for static file)

---

## Appendix A: Benchmark Reference Data

### io_uring vs epoll (Networking)

| Workload | epoll | io_uring | io_uring Ratio | Recommendation |
|----------|-------|----------|----------------|----------------|
| Echo 64B streaming | 1,565K QPS | 506K QPS | 33% | Use epoll |
| Echo 4KB streaming | 669K QPS | 343K QPS | 51% | Use epoll |
| Echo 16KB streaming | 224K QPS | 183K QPS | 82% | Either |
| Ping-pong 1K conns | baseline | +10% | 110% | io_uring if batched |
| Batched request/response | baseline | +25% | 125% | io_uring |

### sendfile Impact

| Metric | read+write | sendfile | Improvement |
|--------|-----------|----------|-------------|
| CPU utilization | ~15% | ~2% | 7.5x less CPU |
| Throughput (large files) | baseline | +8-19% | Significant |
| Context switches | 4/transfer | 2/transfer | 2x fewer |
| Syscalls | 2 (read+write) | 1 (sendfile) | 2x fewer |

### Thread-Per-Core vs Work-Stealing

| Core Count | Monoio (TPC) | Tokio (WS) | TPC Advantage |
|------------|-------------|------------|---------------|
| 1 | 1.0x | ~1.0x | None |
| 4 | 4.0x | ~2.0x | 2x |
| 8 | 8.0x | ~3.2x | 2.5x |
| 16 | 16.0x | ~5.3x | 3x |

---

## Appendix B: Source References

- NGINX benchmarks: blog.nginx.org/blog/testing-the-performance-of-nginx-and-nginx-plus-web-servers
- io_uring design: kernel.dk/io_uring.pdf
- io_uring vs epoll: github.com/axboe/liburing/issues/536, alibabacloud.com/blog/io-uring-vs--epoll
- sendfile: blog.superpat.com/zero-copy-in-linux-with-sendfile-and-splice
- Netflix CDN: netflixtechblog.com/serving-100-gbps-from-an-open-connect-appliance
- picohttpparser: github.com/h2o/picohttpparser, blog.cloudflare.com/improving-picohttpparser-further-with-avx2
- libuv overhead: blog.kazuhooku.com/2014/09/the-reasons-why-i-stopped-using-libuv
- Monoio vs Tokio: github.com/bytedance/monoio/blob/master/docs/en/benchmark.md
- TechEmpower R23: techempower.com/benchmarks
- PostgreSQL 18 io_uring: pganalyze.com/blog/postgres-18-async-io
