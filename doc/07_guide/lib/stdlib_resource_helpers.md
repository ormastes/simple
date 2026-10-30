# Simple std lib: layers, SOSIX and the resource helpers

**TL;DR.** The standard library lives in `src/lib/` and is imported as
`std.<layer>.<module>`. The layer name encodes the memory/concurrency
contract: `nogc_sync_mut` (no GC, synchronous, mutable) holds the hosted
I/O, process, env and resource-scope helpers; `nogc_async_mut` holds the
thread pool, concurrent containers and the unified SOSIX host facade. Host
detection is `host_os()` / `host_is_simpleos()` from
`std.nogc_sync_mut.io.env_ops`. Child processes are run with
`process_run_bounded(cmd, args, timeout_ms, max_output_bytes)`; budgets and
memory evidence come from `std.nogc_sync_mut.io.resource_scope`. Temp paths
come from `sosix_test_temp_dir()` (path only) or `secure_temp_dir()` (creates
a 0700 dir). Parallel work goes through `task_spawn(closure)` in
`std.nogc_async_mut.thread_pool`. `ConcurrentMap` is **not** thread-safe;
there are two fixed-capacity lock-free `i64` maps with different jobs:
`AtomicMap` (mutable `i64 -> i64`: insert, replace, remove, CAS `update`) and
`LocklessMapI64` (insert-once `(key, recipe) -> AsyncRefI64` single-flight
slots). A bounded async resource is `AsyncResourcePool` with affine
`AsyncResourceLease`s. There is no `MemoryReceipt`, `ResourceScope`,
`AsyncResource` or `ProcessLimits` type; the real names are given below.

Related: [misc/stdlib.md](misc/stdlib.md) (SDN, strings, green threads, DB),
[sosix_runtime_library.md](sosix_runtime_library.md) (what the SOSIX facade
can call today, per host), [../language/module_system.md](../language/module_system.md).

---

## 1. Layers and imports

| Layer | Path | What it holds |
|---|---|---|
| `std.nogc_sync_mut` | `src/lib/nogc_sync_mut/` | allocators (`__init__.spl:1-9`), `io/` (env, process, files, resource scope), `fs/`, `concurrent/` (Mutex, RwLock, Channel), `sosix/` (test process boundary, secure temp dir) |
| `std.nogc_async_mut` | `src/lib/nogc_async_mut/` | actor heap/scheduler (`__init__.spl:1-12`), `thread_pool.spl`, `concurrent.spl`, `concurrent/`, `sosix/` (unified host facade) |
| `std.nogc_async_mut.sosix` | `src/lib/nogc_async_mut/sosix/__init__.spl` | re-exports `sosix_platform`, `sosix_run`, `sosix_run_checked`, `sosix_run_bounded_checked`, `sosix_spawn`, `sosix_kill`, `sosix_proc_usage`, `sosix_which`, pty helpers (`:16-25`) |

The four layer names recognised by the lane-boundary lints are
`nogc_sync_mut`, `nogc_async_mut`, `gc_sync_mut`, `gc_async_mut`
(`src/compiler/90.tools/lint/_LintMain/wm_lane_boundary_lints.spl:136`).
Import forms seen in tests:

```simple
use std.nogc_sync_mut.io.env_ops.{env_get, host_os, host_is_simpleos}
use std.nogc_sync_mut.io.process_ops.{process_run_bounded}
use std.nogc_sync_mut.io.resource_scope.{ExecutionResourceClass, execution_resource_scope}
use std.nogc_sync_mut.sosix.test_process.{sosix_test_temp_dir}
use std.nogc_async_mut.sosix.host_facade.{sosix_run}
use std.nogc_async_mut.thread_pool.{task_spawn}
use std.concurrent.{mpsc_queue_new, concurrent_map_new}
```

Application code must not call `rt_*` intrinsics directly; use these std
aliases (see [misc/stdlib.md](misc/stdlib.md) section "Runtime intrinsics").

## 2. Host detection (`env_ops`)

`src/lib/nogc_sync_mut/io/env_ops.spl`:

| API | Line | Returns |
|---|---|---|
| `fn host_os() -> text` | `:102` | `"windows"` when `OS` contains "windows" (`_is_windows_platform`, `:26`); otherwise `uname -s` mapped to `"linux"`, `"macos"`, `"freebsd"`, `"openbsd"`, `"netbsd"`, else the lower-cased uname. Falls back to `"linux"` if `uname` fails (`:106`). Spawns a process: cache the result. |
| `fn host_is_simpleos() -> bool` | `:96` | `SIMPLE_OS_KERNEL == "simpleos"`. `host_os()` can never report SimpleOS (`:97-99`). |

There is no `is_windows` in `env_ops`. Use one of:

- `pub fn is_windows() -> bool` in `src/lib/nogc_sync_mut/platform.spl:95`
  (`host_os() == "windows"`); `platform.spl:54` has its own `host_os()`.
- `pub fn host_is_windows_host() -> bool` in
  `src/lib/nogc_sync_mut/fs/host_path.spl:142`: the cached check the
  hot paths use.
- `sosix_platform()` (`src/lib/nogc_async_mut/sosix/host_facade.spl:89`)
  collapses to the family `"posix"` or `"windows"`.

```simple
use std.nogc_sync_mut.io.env_ops.{host_os, host_is_simpleos}

val os = host_os()
if host_is_simpleos():
    print "SimpleOS kernel"
elif os == "macos" or os == "linux" or os.ends_with("bsd"):
    print "POSIX host: " + os
elif os == "windows":
    print "Windows host"
```

## 3. Resource scopes and memory evidence

`src/lib/nogc_sync_mut/io/resource_scope.spl` (header `:1-5`: Linux
cgroup-v2 observations; typed evidence, never relabelled RSS).

Types:

- `pub enum ExecutionResourceClass` (`:36`): `Unit`, `Integration`, `System`,
  `Qemu`, `Gpu`, `Bootstrap`, `Tiny`, `Standard`, `Large`, `Unbounded`.
- `pub struct ExecutionResourceScope` (`:48`): `resource_class`,
  `budget: ResourceBudget`, `timeout_ms`, `max_output_bytes`.
- `pub struct ExecutionScopeResult` (`:54`): `process`, `budget_decision`.
- `pub struct CurrentExecutionResourceScope` (`:58`): a lease on the current
  process's own cgroup.
- `ResourceBudget` (`:116`) and `ResourceUsage` (`:87`) are in
  `src/lib/common/perf/execution_metrics.spl`; `ResourceUsage` carries
  `wall_ms`, `user_cpu_ms`, `peak_tree_charge_bytes`,
  `peak_direct_child_rss_bytes`, `io_read_bytes`, ... plus
  `evidence_quality: ResourceEvidenceQuality` (`ExactTree`,
  `ExactDirectChild`, `SampledTree`, `ProcessOnly`, `Unavailable`, `:10`).

Functions:

| API | Line | Notes |
|---|---|---|
| `standard_resource_budget(resource_class) -> ResourceBudget` | `:65` | fixed quantities; e.g. `Unit` = 300 s wall, 3 GiB tree charge, 128 pids; `Tiny` = 30 s, 256 MiB; `Unbounded` = all zero |
| `execution_resource_scope(resource_class, timeout_ms = 0, max_output_bytes = 1_048_576)` | `:89` | timeout defaults to the budget's `max_wall_ms` |
| `execution_resource_scope_with_budget(resource_class, budget, max_output_bytes = 1_048_576)` | `:93` | custom budget |
| `run_in_execution_resource_scope(scope, cmd, args) -> ExecutionScopeResult` | `:775` | cgroup v2 if delegated, else `/bin/sh` + `ulimit`, else plain bounded run |
| `run_in_owned_execution_resource_scope(scope, cmd, args)` | `:789` | same, but Windows goes through a JobObject owner (`_run_windows_owned_scope`, `:802`) |
| `run_in_owned_test_resource_scope(scope, cmd, args)` | `:795` | alias used by the test runner |
| `begin_current_execution_resource_scope(scope) -> CurrentExecutionResourceScope` | `:125` | moves *this* pid into a fresh cgroup; `available: false` if that fails |
| `end_current_execution_resource_scope(lease, exit_code) -> ResourceUsage` | `:134` | reads the counters, moves back, removes the cgroup; `ExactTree` evidence or "unavailable" usage |
| `resource_scope_memory_enforcement() -> text` | `:292` | `"cgroup"`, `"systemd-scope"`, `"rlimit-as"` or `"none"` (always `"none"` on Windows and SimpleOS, `:294`) |
| `run_in_systemd_resource_scope(scope, cmd, args, cancel_after_ms = 0)` | `:450` | `systemd-run` transient scope (Linux) |
| `resource_scope_nonnegative_counter_v1(value) -> Option<i64>` | `:550` | strict cgroup counter parser; absence or syntax error is `None`, never 0 |

**"Memory receipts."** There is no `MemoryReceipt` type. The things that act
as receipts are:

- `ResourceUsage` returned by `end_current_execution_resource_scope` and
  carried in `ExecutionScopeResult.process.usage`.
- `ProcessCompletionV1` (`src/lib/nogc_sync_mut/io/process_completion.spl:3`):
  `pid`, `process_generation`, `exit_code`, `signal_number`, `tree_reaped`,
  `timed_out`, `cancelled`, `stdout_digest`, ...; the owned run path maps it
  into `usage.termination` (`resource_scope.spl:848-852`).
- `group_process_memory_receipt_v1(identity, policy, reserved, peak, platform) -> Result<text, text>`
  (`src/lib/common/build_manager/group_process_protocol.spl:132`): the
  encoded builder memory receipt; providers are `cgroup-memory-max` on
  Linux and `job-memory` on Windows, any other platform is an error
  (`:133-136`).
- A pid cap that cannot be enforced (no `bash`/`ksh`/`zsh` for `ulimit -u`)
  fails closed with an exit-125 receipt instead of running unlimited
  (`resource_scope.spl:204-215`).

```simple
use std.nogc_sync_mut.io.resource_scope.{ExecutionResourceClass, execution_resource_scope,
    run_in_owned_execution_resource_scope, resource_scope_memory_enforcement}

val scope = execution_resource_scope(ExecutionResourceClass.Tiny, 10_000)
val result = run_in_owned_execution_resource_scope(scope, "bin/simple", ["--version"])
print "enforcement=" + resource_scope_memory_enforcement()
print "exit=" + str(result.process.usage.exit_code) + " peak=" + str(result.process.usage.peak_tree_charge_bytes)
```

## 4. Temp directories

| API | Line | Behaviour |
|---|---|---|
| `fn sosix_test_temp_dir() -> text` | `src/lib/nogc_sync_mut/sosix/test_process.spl:45` | Returns a path, creates nothing. `$TMPDIR` or `/tmp`; Windows: `$TEMP` or `C:/Windows/Temp` (8.3 names not expanded, `:53-58`); SimpleOS: unresolved (`:59-61`); POSIX: resolved through `cd -- "$1" && pwd -P` so macOS `/tmp` becomes `/private/tmp` (`:34-43`); cached per process (`:32`). |
| `fn secure_temp_dir(parent, prefix) -> Result<text, text>` | `src/lib/nogc_sync_mut/io/file_ops.spl:228` | creates a private 0700 directory under `parent` |
| `sosix_secure_temp_dir_set_parent` / `_set_prefix` / `_make` | `src/lib/nogc_sync_mut/sosix/secure_temp_dir.spl:27,32,37` | the three-step runtime crossing `secure_temp_dir` is built on (`:1-12`) |

```simple
use std.nogc_sync_mut.sosix.test_process.{sosix_test_temp_dir}
use std.nogc_sync_mut.io.file_ops.{secure_temp_dir}

val base = sosix_test_temp_dir()                      # e.g. /private/tmp on macOS
val work = secure_temp_dir(base, "my-tool-")?          # created, 0700
```

## 5. Running processes

`src/lib/nogc_sync_mut/io/process_ops.spl`:

| API | Line | Notes |
|---|---|---|
| `process_run_bounded(cmd, args, timeout_ms, max_output_bytes) -> (text, text, i64)` | `:1454` | the default. Resolves `cmd`, takes a process-governor slot, enforces deadline and output cap |
| `process_run_bounded_bytes(...) -> ([u8], [u8], i64)` | `:1480` | raw bytes |
| `process_run_bounded_native(...)` | `:1461` | requires positive limits, else `-1` |
| `process_bounded_timed_out(exit_code, stderr) -> bool` | `:1535` | true only for exit `-1` plus a trailing timeout marker |
| `process_bounded_kill_signal(exit_code) -> i64` | `:1548` | signal number when exit is `128+signo`; timeout is never a signal |
| `process_run_with_limits(cmd, args, timeout_ms, memory_bytes, cpu_seconds, max_fds, max_procs) -> ProcessResult` | `:2028` | POSIX: wraps in `/bin/sh -c` with `ulimit -v/-t/-n/-u` (`:1956-1964`); Windows: prints `[WARNING] Resource limits not supported on Windows - using timeout only` (`:1936`) |
| `process_run_with_limits_bounded(..., max_output_bytes)` | `:2031` | same plus output cap |
| `process_spawn_redirected(cmd, args, stdout_path, stderr_path, timeout_ms, capture_limit) -> i64` | `:2210` | Windows JobObject capture; `-1` elsewhere |

`ProcessResult` (`src/lib/nogc_sync_mut/io_runtime.spl:150`): `stdout`,
`stderr`, `exit_code`, `limit_exceeded`, `limit_type`.

`process_run_bounded` returns no "hit the cap" flag; a truncated stream is
always strictly longer than `max_output_bytes` (comment in `resource_scope.spl:643-660`), so compare lengths.

The async-layer equivalents are `sosix_run(cmd, args) -> SosixRun`
(`host_facade.spl:201`, 16 MiB per-stream bound) and
`sosix_run_bounded_checked(cmd, args, timeout_ms, max_output_bytes) -> Result<SosixRun, TextIoError>`
(`:184`); `SosixRun` (`:73`) has `stdout`, `stderr`, `exit_code`.

```simple
use std.nogc_sync_mut.io.process_ops.{process_run_bounded, process_bounded_timed_out}

val (out, err, code) = process_run_bounded("git", ["status", "--short"], 5_000, 65_536)
if process_bounded_timed_out(code, err):
    print "git did not finish in 5 s"
elif code != 0:
    print "git failed: " + err
```

## 6. Thread pool and `task_spawn`

`src/lib/nogc_async_mut/thread_pool.spl`:

- `class ThreadPool` (`:14`); `static fn new(num_workers: usize)` (`:38`,
  `0` = CPU count, fallback 4, `:55-59`); `static fn default()` (`:98`);
  `me submit(task_id: usize)` (`:106`); `me submit_batch(task_ids)` (`:117`);
  `me shutdown()` (`:129`); `me shutdown_now()` (`:147`);
  `fn pending_tasks()`, `fn is_idle()`, `fn is_shutdown()` (`:155-171`).
  `submit` takes a task **id**, not a closure. Docstring caveat: "Thread
  creation requires compiled mode or runtime rebuild" (`:53`).
- `fn task_spawn(closure: fn() -> i64) -> TaskHandle` (`:441`) is the
  closure API; it runs through `multicore_green_spawn`. `class TaskHandle`
  (`:268`) has `fn is_done()` (`:275`) and `me join() -> i64` (`:284`).
- `fn default_go_pool() -> ThreadPool` (`:427`) is the process-global pool
  behind `go()`.

```simple
use std.nogc_async_mut.thread_pool.{task_spawn}

fn work(seed: i64) -> i64:
    var x = seed + 1
    for i in 0..10000:
        x = (x * 1103515245 + 12345) % 2147483648
    x

val h0 = task_spawn(\: work(0))
val h1 = task_spawn(\: work(1))
val total = h0.join() + h1.join()
```

(from `test/01_unit/lib/nogc_async_mut/task_spawn_runtime_pool_spec.spl:1-19`).

## 7. Concurrent containers

`src/lib/nogc_async_mut/concurrent.spl` (imported as `std.concurrent`):

| Type | Line | Constructor | State |
|---|---|---|---|
| `MpscQueue` | `:22` | `mpsc_queue_new()` `:49` | `push`, `pop`, `len`, `close` |
| `MpmcQueue` | `:59` | `mpmc_queue_with_capacity(capacity)` `:94` | bounded; `push` returns `bool`, `is_full` |
| `ConcurrentMap<V>` | `:109` | `concurrent_map_new()` `:156`, `concurrent_map_with_shards(n)` `:160` | **compatibility only**: a linear list of entries with no locking (`:110-147`); `with_shards` ignores `n` (`:159`). Do not share across threads without a `Mutex`. |
| `AtomicFlag`, `Once`, `Barrier` | `:167,195,225` | `atomic_flag_new()`, `once_new()`, `barrier_new()` | sync primitives |

Locks and channels for the sync layer: `class Mutex`
(`src/lib/nogc_sync_mut/concurrent/mutex.spl:25`), `class RwLock`
(`rwlock.spl:38`), `class Channel` (`channel.spl:123`).

**Lock-free maps.** Two types, not duplicates; pick by what the value is.

| | `AtomicMap` | `LocklessMapI64` |
|---|---|---|
| File | `src/lib/nogc_async_mut/concurrent/atomic_map.spl` | `src/lib/nogc_async_mut/concurrent/lockless_map_i64.spl` (arena in `lockless_i64_core.spl`) |
| Import | `std.nogc_async_mut.concurrent.{AtomicMap}` (also `std.nogc_async_mut`) | `std.nogc_async_mut.concurrent.lockless_map_i64.{LocklessMapI64, MapError}` |
| Value | plain `i64` (opaque, non-owning) | `AsyncRefI64` result slot with outcome + waiters |
| Mutation | `insert` (replace), `insert_if_absent`, `remove` (tombstone), `update(key, f)` CAS loop | insert-once `request(key, recipe_id)`; no remove, clear or replace by design |
| Errors | `Result<_, AsyncError>`: `CapacityExceeded` past 3/4 load; reserved key `0` and value `i64` min panic with `refusal_for` text | `MapError`: `InvalidCapacity`, `UnsupportedAtomics`, `AllocationFailed`, `Full`, `DescriptorFull`, `RecipeConflict` |
| Storage | `2*capacity + 2` `AtomicI64` handles + one `AtomicBool` guard; `free()` idempotent | one raw arena; `me close_quiescent()` after all users quiesce |
| Use for | shared handle -> handle index, counters | single-flight "compute once, await the outcome" (e.g. `80.driver/cache/reader/tldr_table_v1.spl`) |

`AtomicMap` API: `static fn with_capacity(capacity) -> Result<AtomicMap, text>`
(power of two >= 2), `get`, `has`, `get_or_default`, `insert`,
`insert_if_absent`, `remove`, `update`, `len`, `is_empty`, `capacity`,
`keys`/`values`/`entries` (snapshots, not atomic across slots), `free`. Key
slots are never cleared, so churn over distinct keys permanently consumes
capacity. Neither map is generic; text keys and `<V>` are not provided.

**Async resource.** `class AsyncResourcePool`
(`src/lib/nogc_async_mut/async/resource_pool.spl`; import
`std.nogc_async_mut.async.resource_pool.{AsyncResourcePool, AsyncResourceLease}`,
also re-exported from `std.nogc_async_mut.async` beside `AsyncSemaphore`) hands out a fixed set of
`i64` resources: `static fn with_resources([i64]) -> Result<AsyncResourcePool, text>`,
`me try_acquire() -> AsyncResourceLease?`, `fn acquire() -> Future<AsyncResourceLease>`,
`fn resource(lease) -> i64?`, `me release(lease) -> bool` (false on double or
stale release), `fn lease_error(lease) -> text`
(`"stale resource lease"` / `"foreign resource lease"`), `me close() -> bool`
(refuses while leases are outstanding), `me free() -> bool`. Permits, claims,
generations and the closed/freed flags are all atomics. The scalar async
result handle is still `pub struct AsyncRefI64`
(`src/lib/nogc_async_mut/async_ring/async_ref.spl`), handed out by
`LocklessMapI64`.

Both new types are verified under the interpreter on macOS; a native
real-thread smoke is pending.

## 8. Per-host matrix

| Host | `host_os()` | Process limits | Memory enforcement | Temp dir | Notes |
|---|---|---|---|---|---|
| Linux | `"linux"` | `ulimit` via `/bin/sh`; `ulimit -u` needs bash/ksh/zsh (`resource_scope.spl:204-215`) | `"cgroup"` when cgroup v2 memory is delegated, else `"systemd-scope"`, else `"rlimit-as"` | `$TMPDIR`/`/tmp`, realpath-resolved | the only host with exact tree charge (`ExactTree`) |
| macOS | `"macos"` | `ulimit` via `/bin/sh` | `"rlimit-as"` or `"none"` | `/tmp` resolves to `/private/tmp` (`test_process.spl:37-39`) | JobObject and cgroup paths are not taken |
| Windows | `"windows"` | timeout only (`process_ops.spl:1936`); JobObject capture via `process_spawn_redirected` (`:2210`) and `windows_redirected_*` (`resource_scope.spl:10`) | `"none"` (`:294`); JobObject memory via `windows_redirected_spawn_checked_with_memory` on the owned path (`:822`) | `$TEMP` or `C:/Windows/Temp`, 8.3 names kept | POSIX tools are routed through a Git-for-Windows shell |
| FreeBSD / OpenBSD / NetBSD | `"freebsd"` / `"openbsd"` / `"netbsd"` (`env_ops.spl:110-112`) | same `/bin/sh` + `ulimit` path as Linux | `"rlimit-as"` or `"none"` (no cgroups) | as Linux | no BSD-specific branches in `process_ops`, `thread_pool` or `concurrent` |
| SimpleOS | never; use `host_is_simpleos()` (`env_ops.spl:96`) | plain bounded run (no `/bin/sh`) | `"none"` (`:294`) | `$TMPDIR`/`/tmp` returned unresolved (`test_process.spl:59-61`) | the SOSIX contracts are bound from `src/os/sosix/`, not this capsule (`sosix/__init__.spl:6-8`) |

## 9. Tests

Run with `bin/simple test <relative path>`.

- env/host: `test/01_unit/app/test_host_env_spec.spl`,
  `test/01_unit/hal_env/hal_env_platform_spec.spl`,
  `test/01_unit/lib/io_runtime/shell_output_host_os_no_recursion_spec.spl`
- resource scope: `test/01_unit/lib/nogc_sync_mut/io/resource_scope_evidence_spec.spl`,
  `resource_scope_child_spawn_spec.spl`
- processes: `test/01_unit/lib/io/process_run_bounded_timeout_vs_kill_spec.spl`,
  `test/01_unit/app/io/process_limits_enforcement_spec.spl`,
  `test/02_integration/hal_env/hal_env_process_spec.spl` (uses `sosix_test_temp_dir`)
- thread pool: `test/01_unit/lib/nogc_async_mut/thread_pool_spec.spl`,
  `task_spawn_runtime_pool_spec.spl`, `test/02_integration/lib/thread_pool_async_spec.spl`
- containers: `test/01_unit/lib/nogc_async_mut/concurrent_spec.spl`,
  `concurrent_ds_spec.spl`, `lockless_map_i64_spec.spl`, `atomic_map_spec.spl`,
  `async_resource_pool_spec.spl`
