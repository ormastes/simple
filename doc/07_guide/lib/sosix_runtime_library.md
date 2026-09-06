# SOSIX runtime library (`std.nogc_async_mut.sosix`)

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

```simple
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

## Exact POSIX leg (backed by the seed deployed 2026-09-05)

`std.nogc_async_mut.sosix.posix` — `sosix_posix_open/close/pread/pwrite`,
`@always_inline` over the sffi aliases. `pread`/`pwrite` take a caller-owned
buffer address (`rt_alloc` family) and return bytes transferred or `-errno`.
The externs `rt_fd_pread`/`rt_fd_pwrite` exist in the seed source as of
2026-09-05 and the binary deployed on this host that evening backs them
(`posix_spec` 3/3 on `bin/simple`); on an older binary they return nil and the
spec is red. The surface is re-exported from the capsule `__init__`.

## Not available (do not advertise)

- **Exact POSIX aliases** (`sosix.posix.pread`/`pwrite`): blocked on runtime-owned
  `rt_fd_pread`/`rt_fd_pwrite` externs (plan task C1). No stub exists.
- **Linux io_uring, macOS, Windows providers**: blocked rows in the plan; the
  only hosted provider is the software ring.
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
