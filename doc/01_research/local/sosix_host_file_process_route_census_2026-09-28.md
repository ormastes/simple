# SOSIX hosted file and process route census

Source baseline: `origin/main` at `7ab226395c5`. This is the hosted library
slice of RU-001 in the [SOSIX unification design](../runtime/sosix_unification/simple_sosix_runtime_unification_design_plan_2026-09-05.md),
not a full repository census or evidence that RU-030/RU-040 has passed.
Signatures and routes below were checked in this tree. `src/os/sosix/**` is a
separate SimpleOS provider tree.

| Public surface and signature | Current owner and route | Direct production callers | Profile and migration disposition |
|---|---|---|---|
| `sosix_spawn(text, [text]) -> i64`; `sosix_is_running(i64) -> bool`; `sosix_kill(i64) -> bool` | `host_facade.spl` braced re-exports of `nogc_async_mut/io/process_ops.spl`, itself a re-export of `nogc_sync_mut/io/process_ops.spl` | No in-tree production call outside the facade was found | Hosted process compatibility aliases. Preserve declaration identity; migrate process lifecycle to a SOSIX service only with provider and cancellation/retirement evidence. |
| `sosix_which(text) -> text` | `host_facade.spl` re-exports `nogc_async_mut/env/paths.spl` | `app/llm_caret/pane_backend.spl`, `app/llm_caret/cs_dashboard.spl` | Hosted path lookup; keep it outside a hot request handler or replace with cached startup configuration. |
| `sosix_pty_open(i32, i32) -> i32`; `sosix_pty_spawn(i32, text) -> i64`; `sosix_pty_write(i32, text) -> bool`; `sosix_pty_read(i32, i32) -> text`; `sosix_pty_close(i32) -> bool`; `sosix_pty_is_running(i32) -> bool`; `sosix_pty_default_shell() -> text` | `host_facade.spl` re-exports `std.sys.pty`, whose operations call `rt_pty_*` after argument checks | `app/llm_caret/pane_backend.spl` uses all except read/default-shell | Hosted PTY compatibility route. A SOSIX process/terminal provider must preserve handle retirement and output semantics before replacing it. |
| `sosix_platform() -> text`; `sosix_run(text, [text]) -> SosixRun`; `sosix_proc_usage(i64) -> SosixProcUsage` | `host_facade.spl` adapters over `platform_name` and `process_run`; usage runs `ps -o %cpu=,rss=` on POSIX and returns unavailable on Windows | `pane_backend.spl` uses platform/run; `cs_dashboard.spl` uses proc usage | Synchronous hosted route. The `ps` shell-out is not a native process-stats provider and must not enter a hot SOSIX request path. |
| `sosix_posix_open(text, i32) -> i32`; `sosix_posix_close(i32) -> bool` | `posix.spl` → `nogc_sync_mut/sffi/fs.spl` → `rt_file_open` / `rt_file_close` | No in-tree production caller outside re-export was found | Raw hosted compatibility route; direct libc alias requirement RU-030 remains unproven. |
| `sosix_posix_pread(i32, i64, i64, i64) -> i64`; `sosix_posix_pwrite(i32, i64, i64, i64) -> i64` | `posix.spl` → `file_pread_fd` / `file_pwrite_fd` → `rt_fd_pread` / `rt_fd_pwrite`. Core-C `runtime_native.c` validates and delegates to `rt_file_read_at_fd` / `rt_file_write_at_fd`; the seed interpreter registers separate Rust implementations | No in-tree production caller outside re-export was found | Raw caller-owned buffer route with bytes-or-negative-errno convention. Native direct `pread@plt` / `pwrite@plt` and interpreter/native parity still need artifact and behavior evidence. The Windows core-C helpers use seek plus read/write, so concurrent positioned semantics require a distinct qualified provider. |
| `sosix_file_map(text, i64, i64, bool) -> i64`; `sosix_file_unmap(i64, i64) -> bool`; `sosix_file_map_prefetch(text, i64, i64) -> bool` | `file_map.spl` validates inputs and uses `sffi/fs.spl` `rt_mmap` / `rt_munmap` / `rt_madvise` wrappers; prefetch maps, advises, then unmaps | `app/simpleos_gpu_host/daemon_runner.spl` and `app/test/simpleos_gpu_fallback_wire_probe.spl` use map/unmap | Live hosted mapping route. Preserve capability policy, mapped-region lifetime, and Windows behavior while introducing a memory service. Prefetch has no production caller found. |
| `sosix_time_monotonic_sample_v1() -> Result<u64, text>`; `sosix_time_realtime_sample_v1() -> Result<u64, text>`; `sosix_time_monotonic_now_ns() -> u64` | `time.spl` → `nogc_sync_mut/io/time_ops.spl`; the no-failure `now` helper maps a negative result to zero | No in-tree production caller outside re-export was found | Synchronous hosted clock samples, with distinct monotonic and Unix domains. They do not implement the planned ring-woken timer provider. |
| `sosix_sync_fs_read_at` / `sosix_sync_fs_write_at` (typed capability, buffer, offsets, deadline → `SosixSyncResult`) | `sync.spl` reserves and commits through `SosixHostedFs`, then waits through `SosixSyncWaitDriver` with a 64-wait budget | `compiler/80.driver/cache/worker/three_payload_worker_io_v1.spl` calls read-at using an in-memory object provider; no production write-at caller was found | Canonical ring-shaped sync adapter. That compiler call proves a logical ring route, not native file I/O. Real native wait provider and retirement evidence remain RU-020/RU-031 gates. |

`fs.spl` contains the hosted ring owner and `file_driver.spl` has a software
driver plus a Linux io_uring driver. They are separate from the raw
`sosix_posix_*` aliases; this census does not collapse their different
submission and completion contracts. `process_observation_v1.spl` re-exports
the owned process-observation API from `nogc_sync_mut/io` and is not the
`sosix_proc_usage` shell-out adapter.

Next RU-001 expansion: enumerate the remaining `rt_*` host declarations and
their callers outside this capsule, then record ABI signatures, source owner,
native/interpreter implementation, and one disposition per symbol. RU-030
needs a native object/disassembly check of the actual libc target and errno
behavior before the raw alias row can be marked direct. RU-040 needs a
file-operation differential fixture across interpreter, native, and SMF
paths. No such acceptance is claimed here.
