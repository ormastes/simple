# POSIX Compatibility Profiles (Honest Matrix)

Lane P5 (POSIX truth), SimpleOS production-harden program. Source: master plan
§9 (`doc/01_research/domain/simpleos_production_host_master_plan.md`).

## Why this document exists

SimpleOS is an L4-microkernel, async-first (SOSIX) system. POSIX is a
**compatibility adapter over SOSIX**, not the native model, and it is only
ever honestly partial. Advertising `_POSIX_VERSION=202405L` (full SUSv5
conformance) would be a lie the moment any consumer probes a facility this
system does not actually implement — package managers, `configure` scripts,
and ported servers all branch on that value. **This system MUST NOT define
`_POSIX_VERSION` as `202405L`.** Audit confirms no source file defines
`_POSIX_VERSION` at all today (`grep -rn "_POSIX_VERSION" src/os/libc/
src/os/posix/` — zero hits); that absence is correct and must stay that way
until a specific profile below is actually conformant enough to claim.

## The four profiles

- **Profile A — Simple Native (SOSIX).** Capability/async-first: `Future<Result<T>>`,
  `CancellationToken`, `Deadline`, `CompletionQueue`, `WaitSet`, `AsyncFd`,
  `SharedBuffer`, `ResourceHandle`. This is the actual native API; POSIX calls
  below are adapters over it, not independent implementations.
- **Profile B — POSIX Core.** Files, spawn/exec/wait, env, clocks, signals,
  pipes, sockets, poll/select, terminal — no full-conformance claim.
- **Profile C — POSIX Server.** Profile B + pthreads, futex-like primitives,
  writable/private/shared mmap, file locks, AF_UNIX, robust signals/EINTR,
  process groups/sessions, termios subset, locale/tz subset, dlopen, shm, AIO,
  C dev headers.
- **Profile D — Linux personality (optional, user-space).** epoll, eventfd,
  timerfd, signalfd, `/proc` compat, ioctl translations, namespace/cgroup
  translations.

Port-enabling order (master plan §9): posix_spawn/exec/waitpid → signals+pgroups
→ full FD semantics → pipes+AF_UNIX → poll/select → pthreads+sync →
private+shared mmap → mprotect/msync/munmap → file/record locks →
termios+PTY → dlopen → locale/tz → COW fork → extended compat.

## Facility matrix

Status legend: **implemented** (real, correctness-checked path) · **partial**
(works for a subset of inputs/flags, honestly rejects the rest) · **stub**
(present, returns a real error for everything — no silent success) ·
**absent** (symbol does not exist) · **DISHONEST** (silently reports success
for something not actually done — a defect, tracked below).

| Facility | Profile | Status | Owning file |
|---|---|---|---|
| open/read/write/close/lseek/dup/dup2 | B | implemented | `src/os/kernel/fd_io.spl` (facade: `src/os/posix/fd_io.spl`), `src/os/libc/simpleos_fs.c` |
| FD table (per-process) | B | implemented | `src/os/kernel/fd_table.spl` (facade: `src/os/posix/fd_table.spl`) |
| Async I/O (non-blocking, IPC-backed) | A/B | implemented (legacy; migrating to SOSIX) | `src/os/posix/async_io.spl`, `src/os/posix/async_io_rw.spl` |
| pipe() | B | implemented (ring buffer + notification pair) | `src/os/kernel/pipe_compat.spl` (facade: `src/os/posix/pipe_compat.spl`) |
| fork/execve/spawn/waitpid | B | implemented (sync wrapper); host-Linux passthrough + SimpleOS syscall path both wired | `src/os/kernel/process_compat.spl` (facade: `src/os/posix/process_compat.spl`), `src/os/libc/simpleos_fork.c`, `src/os/libc/simpleos_process.c`, `src/os/libc/simpleos_process_wait.c` |
| Async process control | A/B | implemented | `src/os/kernel/process_async.spl` (facade: `src/os/posix/process_async.spl`) |
| signal()/kill()/sigprocmask()/raise() | B | implemented | `src/os/posix/signal_compat.spl`, `src/os/posix/signal_dispatch.spl`, `src/os/libc/simpleos_signal.c` |
| sockets (AF_INET) | B | implemented over netstack IPC (port 2) | `src/os/kernel/socket_compat.spl` (facade: `src/os/posix/socket_compat.spl`), `src/os/libc/simpleos_socket.c` |
| socket connect state machine | B | implemented | `src/os/posix/socket_connect_semantics.spl` |
| AF_UNIX | C | absent | — (no `sys/un.h` implementation found beyond header; not wired) |
| poll()/select() | B | implemented (notification multiplexing) | `src/os/posix/select_compat.spl`, `src/os/libc/simpleos_poll.c` |
| dlopen/dlsym/dlclose — ELF | C | implemented | `src/os/libc/simpleos_libc_ext.c`, `src/os/posix/dylib_async.spl` |
| dlopen/dlsym/dlclose — SMF | C | partial (stub entry point) | `src/os/posix/dynlib.spl` |
| dlopen/dlsym/dlclose — PE/COFF | C | stub — honestly returns `Invalid` (WS3 not landed) | `src/os/posix/dynlib.spl` |
| mmap() anonymous private | A-equivalent/B | implemented (real syscall 10 path) | `src/os/libc/simpleos_libc.c` |
| mmap() writable MAP_SHARED — libc surface | C | **absent** — fails closed with `EOPNOTSUPP` (was DISHONEST, fixed earlier lane; still unreachable, see kernel row) | `src/os/libc/simpleos_libc.c`; documented in `src/os/posix/mod.spl` |
| mmap() file-backed (any fd) — libc surface | C | **absent** — fails closed with `EOPNOTSUPP` | `src/os/libc/simpleos_libc.c` |
| writable shared file mapping — kernel model | C | **partial (model)** — shared page-cache objects, per-page map refcounts, rights attenuation from the backing handle, msync/last-unmap write-back, frame-residency refcount separate from the map refcount; spec-proven in userspace only. The physical-frame path is coded but **unproven on hardware** (needs the QEMU gate). Not reachable from libc. | `src/os/kernel/memory/vmm_shared.spl`, `vmm_handle_shared_file_fault` in `src/os/kernel/memory/vmm_vma.spl` |
| msync() | C | **absent at the libc surface**; kernel-side `vmm_shared_msync` flushes the shared page cache into the backing file image only | `src/os/kernel/memory/vmm_shared.spl` |
| munmap()/mprotect() | B | implemented | `src/os/libc/simpleos_libc.c` |
| pthread_create/join/detach | C | stub — honestly returns `ENOSYS` | `src/os/libc/simpleos_pthread.c` |
| pthread mutex/attr | C | implemented as single-threaded no-ops (correct: no concurrent thread exists to race) | `src/os/libc/simpleos_pthread.c` |
| pthread_once/TLS (key_create et al.) | C | implemented (single-threaded semantics) | `src/os/libc/simpleos_pthread.c` |
| pthread_cond_* | C | partial (see file — no real kernel wait, single-thread-safe subset) | `src/os/libc/simpleos_pthread_cond.c` |
| pthread_rwlock_* | C | partial (single-threaded semantics) | `src/os/libc/simpleos_pthread_rwlock.c` |
| flock() (BSD file locks) | C | **DISHONEST — always returns 0 for every operation including `LOCK_EX`, with zero lock tracking.** Filed, not fixed this increment (mmap was fixed as the bounded first increment's honest-failure target). Next lane increment should fail closed (`ENOSYS`) or implement real single-node advisory locking. | `src/os/libc/simpleos_filelock.c` |
| termios (tcgetattr/tcsetattr/tcflush/tcdrain/tcsendbreak/tcflow) | C | stub — honestly returns `ENOSYS`, documented reasoning (no `Tty*` syscall id exists yet) | `src/os/libc/simpleos_termios.c` |
| termios struct transforms (cfmakeraw, speed accessors) | C | implemented (pure struct ops, no kernel dependency) | `src/os/libc/simpleos_termios.c` |
| locale (setlocale/localeconv) | C | partial (returns fixed "C" locale state, no real locale DB) | `src/os/libc/simpleos_libc_ext.c` |
| sched_yield | C | implemented (correct no-op: no other runnable thread exists) | `src/os/libc/simpleos_sched.c` |
| shm_open/shmget/shmat (POSIX/SysV shared memory) | C | absent | — (no symbols found) |
| AIO (aio_read/aio_write) | C | absent | — (no symbols found) |
| epoll | D | implemented | `src/os/libc/simpleos_epoll.c` |
| eventfd | D | stub — honestly returns `ENOSYS` | `src/os/libc/simpleos_eventfd.c` |
| signalfd | D | stub — honestly returns `ENOSYS` | `src/os/libc/simpleos_signalfd.c` |
| timerfd | D | stub — honestly returns `ENOSYS` | `src/os/libc/simpleos_timerfd.c` |
| inotify | D | stub — honestly returns `ENOSYS` | `src/os/libc/simpleos_inotify.c` |
| /proc compat, ioctl translation, namespace/cgroup translation | D | absent | — |
| statvfs/fstatvfs | B | implemented | `src/os/libc/simpleos_statvfs.c` |
| utsname (uname) | B | implemented | `src/os/libc/simpleos_utsname.c` |
| dynamic memory (malloc/free family) | A/B | implemented (dlmalloc) | `src/os/libc/simpleos_dlmalloc.c` |

## Row counts by status (as of this audit)

- implemented: 20
- partial: 6 (writable shared file mapping added as **model-only**)
- stub (honest ENOSYS/error): 9
- absent: 7
- DISHONEST (open defect): 1 — `flock()`, filed above; `mmap()` writable-shared/
  file-backed was the second instance and is now fixed (see below)

Counts are facility-line counts in the table above (some rows group closely
related symbols under one status where they share an owning file and
implementation).

## Honest-failure fix landed this lane

`mmap()` in `src/os/libc/simpleos_libc.c` (SimpleOS-kernel syscall branch,
i.e. when `running_on_linux_host()` is false — the Linux-host branch already
passes `flags`/`fd`/`offset` through to a real `syscall(2)` and was never
dishonest) used to silently discard `flags`, `fd`, and `offset` before
dispatching syscall 10, then hand back an anonymous private mapping
regardless of what was requested. A caller asking for `MAP_SHARED|PROT_WRITE`
(the Profile-C cross-process shared-writable case that `src/os/posix/mod.spl`
already documents as **not supported by design**) or for a file-backed
mapping (`fd >= 0`) got back memory that *looked* like success but was
neither shared with other mappings nor backed by the named file. The fix
fails closed with `EOPNOTSUPP` for both cases instead. Anonymous
`MAP_PRIVATE` mappings (the common allocator-style use) are unaffected and
still real (uses the real `simpleos_syscall(10, ...)` path).

Spec: `test/01_unit/os/posix/posix_honest_failure_spec.spl` pins this
contract, plus a companion assertion that `pthread_create()` still honestly
reports `ENOSYS` rather than faking thread creation.

## Writable shared mmap — kernel model landed (lane MMAP), surface still closed

The capability the honest failure above was standing in for now exists in the
kernel, as a **model**, not as a shipped POSIX facility. Read this section
before quoting the matrix.

**What is real.** `src/os/kernel/memory/vmm_shared.spl` implements shared
file-backed page objects: one page-cache page per `(backing handle, file page
index)`, shared by every address space that maps it, with a per-page map
refcount. Rights come from the backing handle and are attenuated deny-wins — a
read-only handle cannot yield a writable shared mapping (`EACCES`), and an
unregistered handle cannot be mapped at all (`EOPNOTSUPP`). Write-back is an
explicit **msync-required** policy: stores are visible to all shared mappings
at once, but reach the backing file image only on `vmm_shared_msync` or when a
page's last mapping goes away. `vmm_mmap` gates VMA kind
`VMM_VMA_SHARED_FILE`, `vmm_handle_shared_file_fault` maps one physical frame
into every faulting address space (one `pmm_ref_page` per mapping, released by
the existing `pmm_put_page` in `vmm_munmap_result`), and munmap flushes frames
into the page cache before releasing them.

A shared page now carries a **frame-residency refcount** distinct from its map
refcount (`vmm_shared_frame_ref` / `vmm_shared_frame_unref`, lane MMAP2).
Residency counts the address spaces holding a live PTE on the frame; the map
count counts mapped regions, which may never have faulted. The identity of the
frame is retired at exactly the moment the last residency ref drops — the same
moment `vmm_munmap_result` issues the final `pmm_put_page`. Without that split,
a region that was mapped but never touched could fault *after* the frame it
inherited had been returned to the allocator, ref-and-map a freed frame, and
expose another process's memory. That was a real defect in the first model
increment and is fixed and spec-covered.

**What is proven.** The byte-level model only, by
`test/01_unit/os/kernel/memory/vmm_shared_mmap_spec.spl` — 9 blocks, 45
examples, 0 failures on both the JIT and
`SIMPLE_EXECUTION_MODE=interpreter`: cross-space visibility, private-mapping
isolation, rights attenuation, refcount/unmap, process-exit teardown,
write-back through a normal file read, frame-residency retirement, and a
deliberate-red calibration block proving the spec can fail.

**What is NOT proven and NOT claimed.**
- The physical-frame path has no test. It touches real page tables and the
  HHDM and needs a real-firmware QEMU run (OVMF pflash — never `-kernel`, never
  `isa-debug-exit`) with two user tasks mapping one file `MAP_SHARED|PROT_WRITE`
  and observing each other's stores, then a host-side read after msync.
- Multi-core TLB shootdown on the write-back/unmap edge is not implemented.
- On-disk persistence: write-back lands in the kernel's file image, not the
  VFS. A `pwrite` in `src/os/kernel/ipc/syscall_spm.spl` is still needed.
- `mmap()` in libc still returns `EOPNOTSUPP`, deliberately. It hard-codes
  `kind = VMA_ANON` / `backing = 0`, the syscall trampoline has no slot for
  `backing_offset` (kernel arg5), and nothing registers the shared object's
  rights. Relaxing the errno before those land would hand userspace a VMA the
  fault path cannot serve.

**SQLite WAL is therefore still blocked.** `xShmMap` in
`src/os/port/sqlite/sqlite_vfs_contract.spl` must keep failing closed. Note for
that contract's owner: the unblock condition is the three wiring items above,
not this model landing.

Design record, remaining wiring, and the exact gate:
`.spipe/writable_shared_mmap/state.md`.

## Follow-up (not fixed this increment)

`flock()` (`src/os/libc/simpleos_filelock.c`) unconditionally returns `0`
(success) for every `operation` argument, including `LOCK_EX`/`LOCK_SH`, with
no lock-state tracking whatsoever — a program relying on it for mutual
exclusion (package managers, embedded databases, build-lock files) gets zero
protection while believing it holds an exclusive lock. This is a second
instance of the same silent-fake-success anti-pattern this lane targets.
Recommended next-increment fix: fail closed with `ENOSYS` until real
single-node advisory locking is implemented, mirroring the `termios` file's
documented-reasoning pattern.
