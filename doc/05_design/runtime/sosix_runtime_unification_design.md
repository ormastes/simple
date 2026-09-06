# SOSIX Runtime Library Unification — Design

**Date:** 2026-09-05
**Status:** Ready for implementation (core milestone). Repo-verified at `56d032e6f0d`, host `aarch64-unknown-linux-gnu`, `bin/simple` = Rust seed.
**Research:** `doc/01_research/runtime/sosix_unification/` (three external passes + `README_tldr.md` verification block). This design records only what the repo check changed or made concrete; rationale that the research already gives is cited, not repeated.
**Plan:** `doc/03_plan/agent_tasks/sosix_runtime_unification_parallel_plan_2026-09-05.md`
**Lane:** `.spipe/sosix_runtime_unification/state.md`
**Architecture authority:** `doc/04_architecture/simple_ring_async_base.md` (ring/task contract), `doc/01_research/local/sosix_gpu_api_extension_final_report.md` (SOSIX-G IDs/tiers), `doc/01_research/local/sosix_wm_renderer_host_interface.md` (host boundary).

## 1. Decision

Unify the **contract and the library**, not every provider. One operation lifecycle, one Future, one service-ID table, one lib-side `sosix` capsule that both hosted code and SimpleOS bind. The core milestone is Linux-hosted + interpreter/native parity + SimpleOS legacy path retired onto the existing v1 positioned stack. GPU proxy transports, non-Linux hosts, and device-initiated queues stay visible as BLOCKED rows with owners (research WP-07..10, GQ-001..012); they do not gate the core.

Performance is a first-class acceptance axis: every task in the plan carries a structural budget (no extra hop, no allocation on rejection, bounded import closure) and a measured before/after against baseline B0 (§7). A change that cannot show its budget held is not done.

## 2. Verified baseline (what exists, with the deltas the research missed)

| Area | Verified at HEAD | Consequence for this design |
|---|---|---|
| Ring/task contract | `src/lib/common/contracts/execution/simple_ring_async_v1.spl` (312 lines): `RingToken`, `RingGeneration`, `RingMappingGrade`, `RingAdmission`, `RingCompletion<Cpl>`, `RingPayloadLease`, `AsyncTaskFrame`, `TaskContext`, `TaskPollResult<T>`, `StacklessAsyncTask` | Reuse verbatim. No new token, admission, or poll vocabulary. |
| Hosted ring | `src/lib/nogc_async_mut/async_ring/simple_ring.spl` (`SimpleRing`, reserve/commit/batch/cancel/reset/telemetry), `software_provider.spl` (`SoftwareRingProvider`, grade `Software`), `mission_adapter.spl`, `future_compat_adapter.spl` | Hosted SOSIX operations are `SimpleRing` submissions; the software provider is the deterministic reference provider for specs. |
| SOSIX core (SimpleOS tree) | `src/os/sosix/core/`: `operation.spl` (203, pure), `capability_ref.spl` (20, pure), `completion.spl` (74), `completion_queue.spl` (71, cap 1024), `wait_set.spl` (104, cap 256, never spins), `sync_wait_adapter.spl` (150, "performs exactly one native wait when `should_wait`"). **None imports `os.kernel.*`.** 56 importers. | These are already the unified lifecycle; they are just filed under `src/os`. Lift to `src/lib/common/contracts/sosix/`, leave `os.sosix.core.*` as `export use` shims. `src/os` importing `std.common.contracts` has 181 precedents. |
| SimpleOS legacy I/O | `src/os/sosix/io_rw.spl` (236): 128 slots, `while not complete: continue` busy-wait, serial write (`fd_type == 6`) returns `count` without emitting bytes, alloc failure -> `-9`. `src/os/sosix/io.spl` (293) carries a **divergent copy** of the same function set (219-line diff, no `fd_type == 6` branch, no exports) with no importer found. Only `src/os/kernel/async_io_rw.spl` imports `io_rw`. | `io.spl` copy is dead by importer count: diff it against `io_rw.spl`, port anything `io_rw` lacks into the G2 rewrite, then delete. `io_rw.spl` is routed onto `sync_wait_adapter` + the v1 positioned stack, then retired. |
| SimpleOS fs descriptor | `src/os/sosix/fs/operation_adapter.spl` (66): imports only `os.sosix.core.operation` and `os.sosix.core.capability_ref` (both pure) | Liftable with the core; becomes `common/contracts/sosix/file_operation_v1.spl` so the lib capsule can reuse the descriptor rules without importing `os.*` or copying them. |
| SimpleOS v1 positioned stack | `src/os/sosix/fs/`: `positioned_syscall_v1.spl` (syscalls 134/135 `SOSIX_FS_PREAD/PWRITE_REGISTERED_V1`), `registered_buffer_client_v1.spl` (64 buffers, owned copies), `completion_pump.spl`, `service_buffer_registry_v1.spl`, `posix_positioned_write_provider_v1.spl`, `operation_adapter.spl` (`0x0101`/`0x0102`, rejects `length == 0`) | This is the SimpleOS provider. No new SimpleOS I/O implementation. |
| Host services (SimpleOS tree) | `src/os/sosix/host/service_contract.spl`: `SOSIX_HOST_DISPLAY_PRESENT 0x1001`, `_READBACK 0x1002`, `SOSIX_HOST_INPUT_NEXT 0x1101`, `SOSIX_HOST_TIMER_DEADLINE 0x1201`, `SosixHostConfigurationSnapshot`; plus display/input producer adapters, `library_capability_adapter.spl`, `configuration_adapter.spl` | Freeze these IDs in the common table next to `0x0101`. Rendering migration is "wire `screen_host.spl` to these", not "design display/input services". |
| Hosted facade | `src/lib/nogc_async_mut/sosix/host_facade.spl` (157): 4 `@always_inline` pass-throughs, 3 adapters; `sosix_proc_usage` shells out to `ps` | Keep. Add `fs`/`time`/`sync`/`posix` siblings; `ps` stays labeled compat, off the hot path. |
| Future/Promise | Three real implementations: `src/lib/nogc_async_mut/async/future.spl` (132) + `promise.spl` (58); `async_host/future.spl` (118, waker/timeout/cancel) + `promise.spl`; `nogc_sync_mut/src/future.spl` (159, synchronous, type-erased `fn(Any)` callbacks). Shims: `nogc_async_mut/src/future.spl` -> `nogc_sync_mut.src.future`, `gc_async_mut/src/future.spl` -> `nogc_async_mut.src.future`. Noalloc: `nogc_async_mut_noalloc/async/poll.spl`. | Canonical = `std.async.future` (`nogc_async_mut/async/future.spl`) polled through `future_compat_adapter`. `async_host/future.spl` becomes the waker-capable executor-side variant; the `src/future.spl` shims re-export the canonical one; `nogc_sync_mut/src/future.spl`'s callback surface is folded into the canonical or deleted, never kept as a third peer. |
| Alias mechanism | `export use m.f as g` -> `E1002`, bug record 2026-09-03 OPEN | Zero-wrapper aliases are `@always_inline` + disassembly gate until fixed (plan task A5). |
| Raw `rt_*` policy | `raw_rt_access.spl` lint = WARNING; `scripts/check/check-no-direct-rt.shs` baseline **7776** forbidden (vcs.md's 12948 is stale); allowlist 215 lines | New `sosix` modules must be allowlisted providers or call existing facades; ratchet must not rise. |
| Exact POSIX leg | No `rt_*pread*`/`rt_fd_read*` positioned primitive in `src/runtime` or `src/lib` (only `rt_fd_read_until`); no bare-libc `extern fn` mechanism in `src/lib` | `sosix.posix.pread/pwrite` needs a runtime-owned extern pair. Recorded in the lane as `runtime-owned-change`, not assumed. |
| Specs | 49 specs in `test/01_unit/os/sosix/`, 4 in `test/02_integration/os/sosix/`, `simple_ring_spec.spl` (262), `mission_adapter_spec.spl`, `operation_core_spec.spl` (136) | Extend these files; no parallel spec tree. |
| Perf baselines | `doc/10_metrics/` has no sosix/ring rows | Plan task H0 creates them before any behavior change. |

## 3. Target module map

```sdn
src/lib/common/contracts/sosix/            # NEW pure capsule (no os.*, no rt_*)
  operation_v1.spl        # lifted verbatim from src/os/sosix/core/operation.spl
  capability_ref_v1.spl   # lifted from capability_ref.spl
  completion_v1.spl       # lifted from completion.spl + completion_queue.spl
  wait_v1.spl             # lifted from wait_set.spl + sync_wait_adapter.spl
  file_operation_v1.spl   # lifted from src/os/sosix/fs/operation_adapter.spl (0x0101/0x0102 descriptor rules)
  service_ids_v1.spl      # frozen ID table + sosix_service_id_is_known()
  error_v1.spl            # SosixError { kind: SosixErrorKind, native_domain: u8, native_code: i32, transferred: u64 }
src/os/sosix/core/*.spl                    # -> one-line `export use std.common.contracts.sosix.<x>.*` each; core/__init__.spl becomes the shim hub (56 importers untouched)
src/os/sosix/fs/operation_adapter.spl      # -> shim over file_operation_v1
src/lib/nogc_async_mut/sosix/
  __init__.spl            # export use of every sibling
  host_facade.spl         # existing, unchanged
  fs.spl                  # sosix_fs_read_at / write_at -> Future<Result<SosixCompletion, SosixError>> over SimpleRing
  time.spl                # sosix_time_deadline (async) ; sosix_time_monotonic_now (sync leaf, existing time_ops)
  sync.spl                # sosix_sync_fs_read_at / write_at: same op, waits via wait_v1 (one native wait, no spin)
  posix.spl               # sosix_posix_pread / pwrite / read / write / close: @always_inline over runtime-owned externs (task C3) — BLOCKED, absent not stubbed
  file_driver.spl         # B5 reference provider on this host: SosixSyncWaitDriver over the typed path-positioned io aliases (not the POSIX leg)
  # provider.spl dropped 2026-09-05: the ring is the software provider; a SimpleRing passed as an argument is a copy under the interpreter
src/lib/nogc_async_mut/async/future.spl    # canonical Future; async_host/future.spl = executor variant; src/future.spl shims -> canonical
src/lib/common/ui/screen_host.spl          # calls sosix host service IDs 0x1001/0x1002/0x1101/0x1201 (task E1)
```

Ownership rules that the plan enforces per task: `common/contracts/sosix` imports only `std.common.contracts.execution`; `nogc_async_mut/sosix` imports `common/contracts/*`, `async_ring/*`, and existing facades (`std.nogc_sync_mut.io_runtime`, `io.time_ops`); `src/os/sosix/**` imports `std.common.contracts.sosix` and kernel modules, never `std.nogc_async_mut.sosix`; `src/compiler/**` and `src/app/**` import `std.nogc_async_mut.sosix` only.

## 4. Contracts

### 4.1 Operation lifecycle (unchanged semantics, one owner)

`SosixOperationId{slot,generation}` + `SosixOperationSlot` state machine from `operation_v1` is the single lifecycle. Mapping to the ring: a hosted `sosix_fs_read_at` reserves on `SimpleRing`, commits, and records the `RingToken` inside the operation record; completion arrives as `RingCompletion` -> `sosix_operation_complete` -> `SosixCompletion` published to a `SosixCompletionQueue`. Two additions the research asked for and the core lacks:

- **Retirement**: `SosixOperationSlot` gains no new field. Retirement is the ring's `RingPayloadLease` release; `sosix_operation_release` is only legal after the lease is released. Enforced in `fs.spl`, tested by "timeout then late completion cannot release the lease".
- **Generation exhaustion**: `operation_v1` wraps to 1 today. Change to fail closed: when `generation == 0xFFFF_FFFF`, `sosix_operation_release` returns `accepted: false, reason: "generation-exhausted"` and the slot stays terminal. Wrap-to-1 was never exercised by a spec; add one that proves the new behavior and one that proves 56 importers still compile (shim parity).

### 4.2 Async / sync policy

- Async default: `fs.read_at/write_at`, `time.deadline`. They return a `Future` whose `poll` goes through `poll_future_compat` with the operation's `RingToken` as the wait token. No inline blocking, no `.wait()` inside poll.
- Sync leaves stay sync: `time.monotonic_now`, capability validation, `try_take` on a completion queue.
- Typed sync adapter: `sync.fs.read_at` = same reserve/commit, then `SosixSyncWaitAdapter` drives exactly one native wait per `should_wait`. The native wait on hosted Linux is the existing thread/condition primitive behind `std.nogc_async_mut.async_host`; on SimpleOS it is the kernel wait already used by `sync_wait_adapter` callers. `io_rw.spl`'s spin loop is replaced by this.
- Exact POSIX leg: `posix.pread(fd, ptr, len, off) -> i64` with errno semantics preserved by the runtime extern. Not typed, not capability-checked, allowlisted as a provider module.

### 4.3 Error vocabulary

One `SosixError` in `error_v1`. `kind` enumerates `Unsupported`, `InvalidCapability`, `InvalidBuffer`, `QueueFull`, `Canceled`, `TimedOut`, `Native`. Status mapping is fixed in one place, `sosix_error_from_status`: `-11` (EAGAIN) -> `QueueFull`, `-110` -> `TimedOut`, `-125` -> `Canceled`, other negatives -> `Native{native_code}`. Kernel-facing `i64` returns (the `io_rw` route) emit `-11` on slot exhaustion instead of today's `-9`; `-5` on VFS failure stays `Native`. No `text` in the hot-path record; `sosix_error_describe` formats on demand.

### 4.4 Frozen service IDs

`service_ids_v1.spl` holds exactly the IDs that exist today: `0x0001..0x0003` (trace/cancel/health), `0x0101..0x0103` (fs), `0x0201..0x0204` (net), `0x0301..0x0302` (ipc), `0x1001,0x1002` (display), `0x1101` (input), `0x1201` (timer). Adding an ID is a contract-owner change (plan stream A) with a spec asserting the table is duplicate-free.

## 5. What stays out

Renderer semantics (DrawIR, Engine2D, layout), compiler IR, value/string intrinsics, allocator policy, `SimpleCompilerDriverV1` descriptor, SMF loader format. `draw_ir_runtime_queue.spl`'s submit-then-drain is a rendering-lane fix scheduled after E1, not a SOSIX contract change. No grammar change; `@sosix_api` metadata stays as documented in the SOSIX-G report and is not extended here.

## 6. Runtime boundary

`chosen_path: reuse-facade` for everything except `posix.spl`, which is `runtime-owned-change`: two externs `rt_fd_pread(fd, ptr, len, off) -> i64` and `rt_fd_pwrite(...)` implemented in the Rust seed runtime with a C twin in `src/runtime` (thin `pread`/`pwrite` calls; result is bytes transferred or `-errno` — an interpreted caller cannot read thread errno before the interpreter clobbers it, and `-errno` is the io_uring completion convention the SOSIX status already uses) with a Simple twin per `doc/07_guide/os/hal/pure_simple_hal.md`, registered in `runtime_symbols.rs` at the `Sys` tier, and added to the no-direct-rt allowlist for `posix.spl` only. Until they land, `posix.spl` is absent (not a stub) and its plan row is BLOCKED with the extern pair as the unblock condition. Rejected shortcuts: seek+read emulation of `pread`, a `text`-returning read, declaring the extern in a spec, any `.smf` or fixture bypass. The B5 `file_driver.spl` (2026-09-05) uses the typed path-positioned aliases as a *reference provider* behind the ring on this host; it is not the exact POSIX surface and does not close this row.

## 7. Performance design

Structural budgets (pass/fail, checked per task):

| Path | Budget | Gate |
|---|---|---|
| `sosix.posix.pread` native | call site -> `pread@plt`, no intermediate symbol, no allocation | `objdump -d` of a native-built probe; sabotage by removing `@always_inline` must show the wrapper |
| `sosix.sync.fs.read_at` hosted | 1 reserve + 1 commit + ≤1 native wait; zero heap allocation after ring creation | `SoftwareProviderCounters` + allocation counter in spec |
| `sosix.fs.read_at` async | rejection path allocates nothing (`RingAdmission` value only); completion wakes exactly one token | counters; "completion-before-poll" and "stale token" specs |
| Import closure | `bin/simple deps normal <entry>` exclusive count for `std.nogc_async_mut.sosix` ≤ 25 files; `common/contracts/sosix` ≤ 8 | deps receipt pasted in task report |
| File size / lint | every new `.spl` ≤ 300 lines (lint cost is superlinear per file, `.claude/rules/commands.md`) | `wc -l`; lint one file at a time |
| Startup | `bin/simple --help` cold time and RSS unchanged within noise vs B0; `sosix` not in the `--help` closure | `sh scripts/check/check-startup-size-performance-audit.shs` before/after |
| SimpleOS idle | after `io_rw` retirement, a blocked sync read yields (no CPU spin) | QEMU guest counter: idle loop iterations while a read is pending == 0 |

Measurements (recorded, not thresholds yet): p50/p95 of 4 KiB `pread` direct vs `posix.pread` vs `sync.fs.read_at` vs `await fs.read_at` on the software provider, 10k iterations, same binary, bracketed by `readlink -f bin/simple && stat -c '%s %y' ...` before and after. Stored under `doc/10_metrics/runtime/sosix_unification_<date>.md` with the exact commands. Never A/B across two trees.

## 8. Verification shape

Specs extend existing files where one covers the module, one new spec per new module, all run as `bin/simple test <spec> --no-session-daemon` reading the `Results:` line. Every behavior task ships a sabotage arm that turns green to red. Mandatory scenarios (mapped from research V01..V32 to what the core milestone can prove on this host):

- V04/V05 raw-vs-typed semantics: partial read, EOF, zero length (POSIX raw returns 0; typed `read_at` rejects `length == 0` at the descriptor as today, documented), invalid capability rejected before effect.
- V06/V07/V08/V09: async does not block a sibling task; failed reservation has no completion; queue-full is `QueueFull` not a bad descriptor; stale generation cannot complete or wake.
- V11/V12: timeout then late completion cannot release the lease; generation exhaustion fails closed.
- V15: same fixture under `--mode=interpreter` and `--mode=native` for `fs.read_at` on the software provider.
- Shim parity: all 56 `os.sosix.core` importers still compile (`bin/simple deps fast` on one SimpleOS entry that pulls them).
- io_rw retirement, two evidence levels: unit level on this host (no spin loop, `-11` on exhaustion, serial branch calls the UART owner) closes now; the serial-bytes-observed row needs `scripts/check/check-sosix-qemu-matrix.shs` under a pure-Simple compiler accepted by `simple_binary_is_valid`, and this host runs the seed, so that row is BLOCKED with the deploy as its unblock. The previous fabricated `count` return is the sabotage arm at both levels.

BLOCKED rows kept visible in the plan with owner and resume command: Linux io_uring provider, macOS/Windows providers, GPU proxy (G1) transport, SimpleOS device-initiated queues, `export use ... as` fix (compiler lane).

## 9. Rejected alternatives (delta to research)

- Create `src/lib/nogc_sync_mut/sosix/` as the sync root: rejected, default tier rule puts new stdlib surface in `nogc_async_mut` first; sync lives in `nogc_async_mut/sosix/sync.spl`.
- Write a new SimpleOS async I/O implementation for WP-09: rejected, the v1 positioned stack exists; `io_rw.spl` is retired onto it.
- Design display/input services: rejected, `src/os/sosix/host/service_contract.spl` already defines them; wire, do not redesign.
- Keep both Future implementations as peers: rejected, one canonical + one executor variant + shims.
