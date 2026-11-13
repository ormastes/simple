# `std.common.fault_detection` is imported but does not exist

Date: 2026-11-13
Status: fixed (2026-11-13)
Severity: P3

`src/app/interpreter/core/watchdog.spl` and `src/app/interpreter/core/execution_guard.spl`
both imported `is_timeout_exceeded`, `set_timeout_exceeded` and `reset_timeout` from
`std.common.fault_detection`. No such module existed under `src/lib`. `execution_guard` is
used by `control/control/loops.spl` and `call/function_exec.spl`, so the pure-Simple
interpreter's timeout poll could not load.

Found while fixing `watchdog_externs_unregistered_module_uncalled_2026-07-08.md`.

## Fix

`src/lib/common/fault_detection.spl` is a pure-Simple port of the seed's
`simple_common::fault_detection` (`src/compiler_rust/common/src/fault_detection.rs`). It adds
no extern.

- **Timeout.** The seed's `TIMEOUT_EXCEEDED` atomic is set by a Rust thread and has no backed
  read from Simple. The module instead keeps its own flag plus a deadline on the monotonic
  clock (`time_sample_monotonic_nanos_or_failure`, backed in both the seed and C lanes).
  `set_timeout_limit_secs(secs)` arms it, `is_timeout_exceeded()` polls it and latches.
  `watchdog.spl` now arms the deadline in `start_watchdog` and disarms it in `stop_watchdog`,
  next to the existing `WatchdogManager` call. A failed clock sample fails closed.
- **Recursion depth.** `increment_recursion_depth` refuses at the limit and leaves the depth
  unchanged, as the seed's `push_call_depth` does; `decrement_recursion_depth` saturates at 0.
  With detection disabled the seed does not count depth at all; this port keeps counting
  and only stops refusing, so increments and decrements stay balanced across a toggle.
- **Guard release.** `exec_function` (`call/function_exec.spl`) relied on `ExecutionGuard`
  being dropped at scope exit. It is not: measured on the seed, a function that binds the
  guard and returns leaves the depth at 1, which would report a false stack overflow after
  1000 calls. `exec_function` now calls `guard.drop()` explicitly, also when argument
  binding fails.
- `execution_guard.spl` imported `check_faults` and `FaultKind` but never used them, and
  neither exists in the Rust original; the import was dropped. `push_call_depth`, which
  `function_exec.spl` imports, was missing from its `export` list and was added.

## Evidence

Spec: `test/01_unit/lib/common/fault_detection_spec.spl` (seed `simple-seed-v4`, aarch64).

- Red (commit `d41cdafebeb`): `outcome=ERROR declared>=10 executed=0 passed=0 failed=0`.
- Green: `outcome=OK declared>=11 executed=11 passed=11 failed=0`.
- `watchdog_manager_spec.spl` unchanged at 4/4.

## Left over

- The Simple state is separate from the host runtime's. When the pure-Simple interpreter is
  hosted by the seed, the seed keeps its own `TIMEOUT_EXCEEDED`, `RECURSION_DEPTH` and
  `MAX_RECURSION_DEPTH`; `rt_fault_set_max_recursion_depth` and friends do not change the
  Simple module's limits, and nothing forwards the other way.
- An armed poll costs one monotonic clock sample per loop iteration (an unarmed poll is a
  flag read). Not measured.
- The deadline is only checked when polled: code that never reaches `check_loop_safety` /
  `check_safety` (for example a blocking extern call) is not interrupted. The C runtime lane
  still has no timer thread (`rt_fault_set_timeout` there records `SIMPLE_TIMEOUT_SECONDS`).
- Expiry is tested through the pure `timeout_deadline_passed` predicate; no spec waits for a
  real deadline, and none runs the module under native codegen.
- `src/app/interpreter/call/function_exec.spl` itself still does not load on the seed, for a
  reason outside this bug: importing it fails with `error: semantic: variable `from` not
  found`, after deprecation warnings on the relative `from ..expr import {...}` lines of the
  `call/` package (first seen at `call/class_instantiation.spl:7`). Not root-caused. So the
  explicit `guard.drop()` in `exec_function` is checked by source and by the guard-level
  spec scenario, not by running `exec_function`. `loops.spl` was not load-tested either.
- If a runtime ever does call `drop()` at scope exit, the explicit call makes it run twice;
  the decrement saturates at 0 but the count would be one low.
- `request_interrupt` in `execution_guard.spl` still has no caller wired from
  `rt_init_signal_handlers`; not part of this bug.
