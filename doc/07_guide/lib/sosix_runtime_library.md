# SOSIX runtime library (`std.nogc_async_mut.sosix`)

## Host process integration workflow — 2026-10-29

Read the [host coordination contract](../../05_design/runtime/sosix_runtime_unification_design.md#2026-10-29-host-process-coordination-contract)
before editing a host adapter. The process baseline is `release/1.0.0` at
`f0d6c75f235` (#5234); older file-provider status below is dated and separate.
Mac has a cooperative native snapshot runner and API. Strict V4 remains
unavailable on Mac; Linux/Windows/FreeBSD/SimpleOS claims require their own
profile-specific host receipts.

1. Fetch the intended integration branch and inspect active lanes/dirty paths.
   Create a unique isolated worktree (sparse where useful) from the recorded
   base. Preserve unrelated worktrees, staged files and runtime artifacts.
   State the host/profile, owner, shared paths and dependent PRs before edits.
2. Agree shared ABI and lifecycle changes with the integration owner. Reuse
   the versioned SOSIX owners; keep host mechanisms in their adapter. Land a
   shared-contract prerequisite before consumers, or explicitly stack the
   consumer PR on it. Do not independently rename facade functions, reorder
   receipt fields or broaden capability bits on each OS.
3. Write the acceptance manual and executable SSpec, then demonstrate RED
   against the missing or incorrect behavior before implementation. A
   missing-host implementation placeholder must fail immediately with an
   explicit assertion/failure; no empty class, successful no-op, fabricated
   receipt or pass-todo counts as an adapter. Keep public unavailable-provider
   responses truthful and separate from internal development placeholders.
4. Implement and run the real host gate to GREEN. Include refusal before
   spawn, argv/env/cwd, output bounds, timeout/cancel, descendant retirement,
   handle reuse/fork authority and ACK behavior as applicable. Test strict
   requirements with adversarial cases, including escapes and image mutation;
   a cooperative-profile pass cannot discharge a strict-profile requirement.
5. Record exact source/runtime identity, host/architecture, selected profile,
   command, executed/passed/failed/skipped counts, and retained output. Mark
   native C, diagnostic P1, deployed native Simple and P2 evidence separately.
   A mock, allocator stub, foreign-host skip or expected strict refusal cannot
   silently become an end-to-end provider pass. Run affected ABI/registration,
   source-list, fallback-compile and direct-environment guards as appropriate.
6. Integrate only owned paths on the latest target branch. Inspect concurrent
   changes in shared files; reconcile semantics with their owner rather than
   taking an entire side of a conflict. Rerun checks affected by that change,
   obtain independent review of the final commit and read PR comments before
   merging. Land through a PR into the recorded target branch; do not merge
   another agent's active draft or bypass a failure caused by this change.
7. Update this matrix/guide and evidence links with the merged SHA. A merged
   source change is not deployment: report outstanding rebuild, runtime-route
   qualification and host validation explicitly. Never rebuild or replace a
   shared P2 artifact as an incidental documentation or adapter task.

### Using the landed cooperative Mac surface

The standalone source is
`src/runtime/tools/sosix_darwin_snapshot_runner.c`. Its explicit profile is
`trusted-snapshot-group`; `sealed-v4` rejects before executable acquisition.
The native runtime facade is `std.nogc_sync_mut.io.darwin_snapshot_v1`:
`darwin_snapshot_capabilities`, `darwin_snapshot_start`,
`darwin_snapshot_poll`, `darwin_snapshot_cancel`, `darwin_snapshot_output`,
and `darwin_snapshot_ack`. Only explicit profile `1` is accepted by start.
Invocation is `[absolute executable, cwd, args...]`; environment is complete,
not inherited by implication. Limits are wall/grace/cleanup nanoseconds and
stdout/stderr capture caps, in the order documented by the facade.

Use a locally owned Mach-O under the documented trust assumptions. Keep the
opaque handle until poll reports frozen; errors and cancellation do not free
it. Read replayable frozen output, then ACK to consume ownership. Poll has a
bounded wait. Do not replace the handle with a PID or share authority across
fork. Capability checks must retain sealed-image, escaped-descendant and
platform-signed-copy qualification as unavailable. Existing strict runner
admission is unchanged; no automatic fallback to this trusted profile exists.

Run on the Mac host from a source-matched checkout:

```sh
sh scripts/check/check-sosix-darwin-snapshot-runner.shs
sh scripts/check/check-sosix-darwin-snapshot-api.shs
```

See the [runner acceptance/evidence](../../06_spec/03_system/lib/process/darwin_snapshot_runner_spec.md)
and [API acceptance/evidence](../../06_spec/03_system/lib/process/darwin_snapshot_api_spec.md).
The API check compiles the production process owner with local value/array
allocator stubs. Its P1 SSpec executes that C gate; interpreter authority
methods reject unavailable providers. Neither this test nor an import-only
facade probe proves a deployed native Simple call path. No P2 rebuild or
strict Mac provider qualification was performed for #5233/#5234.

## Current qualification note — 2026-10-11

Availability statements elsewhere in this guide are dated observations, not a current cross-platform certification matrix. Use the [variation/SOSIX integration](../../05_design/compiler/perf/item5_shared_provider_interfaces_2026-10-09.md#2026-10-11-variation-and-sosix-integration) and exact source-matched provider receipts for support claims.

A shared operation API may use a portable synchronous provider; it does not establish native asynchronous OS completion. Exact POSIX aliases require matching return/error, offset, cancellation and lifetime behavior, not similar function names. CUDA-off CPU execution, C CUDA provider execution, environment-variant GPU-task binding and SOSIX-G qualification are separate capabilities. Timeout does not free an in-flight buffer. No arbitrary CUDA/Metal/Vulkan provider or worker profile becomes supported through this documentation update.

In particular, raw bytes-or-negative-errno results are not POSIX `-1` plus `errno`. Positioned-write parity must account for `O_APPEND` behavior on the selected provider; a spelling-compatible alias is insufficient. Preserve the typed raw-result contract until a tested translation provides exact POSIX semantics.

One library for OS-service access, bound by hosted Simple code and by SimpleOS
alike. Contracts are pure values under `std.common.contracts.sosix`; the hosted
composition lives in `std.nogc_async_mut.sosix`; SimpleOS binds the same
contracts from `src/os/sosix/**` (its old `os.sosix.core.*` names are shims).
Design: `doc/05_design/runtime/sosix_runtime_unification_design.md`.

## What you can call today (verified 2026-09-05, Rust-seed binary)

| Surface | Import | Notes |
|---|---|---|
| Frozen service IDs | `std.common.contracts.sosix.service_ids_v1` | `SOSIX_ID_*`, `sosix_service_id_is_known`; adding an ID is a contract-owner change |
| Typed errors | `std.common.contracts.sosix.error_v1` | `SosixError{kind,native_domain,native_code,transferred}`; `sosix_error_from_status(-11/-110/-125)` |
| Operation lifecycle | `std.common.contracts.sosix.operation_v1` | slot/generation state machine; generation exhaustion fails closed (`generation-exhausted`) |
| Completions and waits | `completion_v1`, `wait_v1` | bounded completion FIFO, one-shot wait set, spin-free sync wait protocol |
| Positioned descriptors | `file_operation_v1` | `0x0101`/`0x0102`, rejects `length == 0` |
| Async positioned I/O | `std.nogc_async_mut.sosix.fs.SosixHostedFs` | `read_at`/`write_at` -> `SosixFsSubmit`; `poll(op)` -> `TaskPollResult`; `pump()`; `release` refused until the ring retired the lease |
| Sync positioned I/O | `std.nogc_async_mut.sosix.sync.sosix_sync_fs_read_at` | same submission, exactly one native wait per completion via a `SosixSyncWaitDriver`; bounded retry budget, never spins |
| Time leaves | `std.nogc_async_mut.sosix.time` | `sosix_time_monotonic_now_ns` (sync), deadline helpers |
| Process/env facade | `std.nogc_async_mut.sosix.host_facade` | unchanged |

Minimal async use (software provider; a real provider services the ring instead of `service_one`):

```simple
use std.nogc_async_mut.sosix.fs.{SosixHostedFs}
use std.common.contracts.sosix.capability_ref_v1.{SosixCapabilityRef, SosixBufferRef}

val fs = SosixHostedFs.create(91u64, 7u64, 8).unwrap()
val submit = fs.read_at(SosixCapabilityRef(slot: 3, generation: 1), SosixBufferRef(slot: 5, generation: 1), 0u64, 0u64, 4096u64, 0u64)
# ... provider completes; then:
fs.pump()
match fs.poll(submit.operation):
    case TaskPollResult.Ready(result): ...   # Result<SosixCompletion, SosixError>
    case TaskPollResult.Pending(token): ...  # the exact RingToken that will wake you
fs.release(submit.operation)
```

## Real files on this host: the reference file driver

`SosixHostedFileDriver` (`std.nogc_async_mut.sosix.file_driver`) services ring
submissions with real positioned reads and writes through the typed
`std.nogc_async_mut.io` aliases. Register a path and a buffer, then use the
sync leg:

```simple:skip
use std.nogc_async_mut.sosix.{SosixHostedFs, SosixHostedFileDriver, sosix_sync_fs_write_at, sosix_sync_fs_read_at}

val fs = SosixHostedFs.create(owner_id, ring_id, 2).unwrap()
val driver = SosixHostedFileDriver.create()
val file = driver.open_path("/tmp/example.txt")
val source = driver.buffer_from("unified sosix bytes")
val written = sosix_sync_fs_write_at(fs, driver, file, source, 0u64, 0u64, 19u64, 0u64)
val sink = driver.buffer_from("")
val read = sosix_sync_fs_read_at(fs, driver, file, sink, 8u64, 0u64, 5u64, 0u64)
driver.buffer_bytes(sink)        # "sosix"; read.completion.transferred == 5
```

A short read reports `partial_progress` with `transferred < length`; a missing
file completes with `SOSIX_ERROR_NATIVE` and `native_code == -5` (the alias
reports no errno; the fd-level extern pair in plan task C1 replaces that
stand-in). Every synchronous call releases its ring slot on return, so a
capacity-1 ring serves call after call. Custom providers implement
`SosixSyncWaitDriver` and drive `fs.take_next()` / `fs.complete_taken(...)`.

Measured cost on the Rust seed interpreter (aarch64, 2026-09-05): one unified
read costs about 38× a direct positioned read — interpreter tax on ~40 calls,
one ring hop, no allocation on the hot path. Report:
`doc/10_metrics/runtime/sosix_unification_perf_report_2026-09-05.md`.

### Windows and macOS native provider status (2026-09-21)

`SosixHostedFileDriver.service` performs its positioned read or write before
publishing the completion. Its passing filesystem specs establish the portable
fallback's behavior; they do not establish asynchronous OS file submission.
There is no platform provider selection in this driver.

Native backend source exists in `src/runtime/platform/async_windows.c` (IOCP)
and `async_macos.c` (kqueue with a file worker pool). However, those files and
their `async_driver.c` bridge are absent from all three runtime source lists.
The bridge also disagrees with `runtime.h` on three function signatures. On
Windows, LLVM 23.1.1 compiles the IOCP file by itself, but rejects the bridge
when checked against that public header. The Rust seed's separate
`rt_driver_*` implementation returns `-38` for Windows file operations.

TODO 306 remains **OPEN**. A native provider requires a reviewed runtime ABI
and build integration, a SOSIX adapter that retains operations and buffers
until completion or cancellation, and platform behavioral evidence. See the
[blocker report and reproduction](../../08_tracking/todo/sosix_c5_native_provider_runtime_blockers_2026-09-21.md).

## Exact POSIX leg (backed by the seed deployed 2026-09-05)

`std.nogc_async_mut.sosix.posix` — `sosix_posix_open/close/pread/pwrite`,
`@always_inline` over the sffi aliases. `pread`/`pwrite` take a caller-owned
buffer address (`rt_alloc` family) and return bytes transferred or `-errno`.
The externs `rt_fd_pread`/`rt_fd_pwrite` exist in the seed source as of
2026-09-05 and the binary deployed on this host that evening backs them
(`posix_spec` 3/3 on `bin/simple`); on an older binary they return nil and the
spec is red. The surface is re-exported from the capsule `__init__`.

## File mapping: two distinct operations (2026-09-19)

`std.nogc_async_mut.sosix.file_map` is the ONLY host-mapping path in Simple
product code; `std.nogc_sync_mut.io.file_ops` no longer carries `file_mmap`
(the raw `rt_mmap`/`rt_munmap`/`rt_madvise` externs live behind
`std.nogc_sync_mut.sffi.fs` aliases and are not imported anywhere else).

| Op | Purpose | POSIX | Windows |
|---|---|---|---|
| `sosix_file_map(path, size, offset, readonly) -> i64` + `sosix_file_unmap(addr, size)` | ACTUAL access: read (or write) the bytes through the address | `mmap(2)` / `munmap` | `CreateFileMapping` + `MapViewOfFile` / `UnmapViewOfFile` |
| `sosix_file_map_prefetch(path, size, offset) -> bool` | CACHING: startup warm-up of the page cache | `mmap` + `madvise(WILLNEED)` + `munmap`, composed in Simple | **no-op, returns true, maps nothing** |

Bounds contract (runtime-owned, identical in the Rust owner, `runtime_native.c`
and the `platform/*` headers): 0 on any failure, `size > 0`, `offset >= 0`,
`offset + size` must not overflow and must lie inside the file; `offset` must be
page-aligned as `mmap` requires. The Rust owner additionally consults the
sandbox (`READ_FILE`, and `WRITE_FILE` for `readonly: false`); the core-C
runtime has no sandbox and this facade adds no policy hook. Verified on Linux
by `scripts/check/check-file-map-c.shs` (both C owners) and the interpreter
probe in this change's report; the Windows branches are written, not compiled.

## Not available (do not advertise)

- **Exact POSIX aliases** (`sosix.posix.pread`/`pwrite`): blocked on runtime-owned
  `rt_fd_pread`/`rt_fd_pwrite` externs (plan task C1). No stub exists.
- **Linux io_uring, macOS, Windows native providers**: blocked rows in the
  plan. `SosixHostedFileDriver` provides synchronous host filesystem service
  through the ring; Windows/macOS native backend source is not integrated.
- **GPU proxy (SOSIX-G G1) and SimpleOS device-initiated queues**: blocked rows.
- **Renaming re-export** (`export use m.f as g`): still `E1002`; facades use
  `@always_inline` pass-throughs.

## Interpreter trap worth knowing

A class read from a **field** (`self.ring`) and passed as an argument is a
copy under the seed interpreter; a class held in a **local** or parameter is
shared. `SosixHostedFs.service_one` therefore drives `self.ring` directly instead
of handing it to the provider wrapper (measured 2026-09-05: takes=1,
successes=0 through the wrapper).

## Verification

```bash
bin/simple test test/01_unit/lib/nogc_async_mut/sosix/fs_async_spec.spl --no-session-daemon   # 6/6, also --mode=native
bin/simple test test/01_unit/lib/nogc_async_mut/sosix/fs_sync_spec.spl  --no-session-daemon   # 4/4
bin/simple test test/01_unit/lib/common/contracts/sosix/service_ids_spec.spl --no-session-daemon
sh scripts/check/check-sosix-capsule-boundaries.shs   # PASS — import directions, ≤300 lines, direct-rt src ceiling
```

Baseline and budgets: `doc/10_metrics/runtime/sosix_unification_baseline_2026-09-05.md`.
Plan and blocked rows: `doc/03_plan/agent_tasks/sosix_runtime_unification_parallel_plan_2026-09-05.md`.
