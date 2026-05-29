# Bug: Test runner CPU throttle dropped to 1 thread, effectively stalling full suite

**Date:** 2026-05-27
**Severity:** Medium
**Component:** src/app/test_runner_new/

## Symptom

`bin/simple test` (full suite, 8244 tests) starts with 32 threads but drops to
1 thread within ~18 tests when CPU hits 96%. At ~500ms/test on 1 thread, the
full suite would take ~70 minutes. Appears to hang from the user's perspective.

## Observed Behavior

```
Starting parallel execution with 32 threads (CPU threshold: 70%, memory threshold: 70%)
[1/8244] PASS parser_spec.spl (46ms, 32 threads)
...
[18/8244] PASS watcher_app_spec.spl (466ms, 32 threads)
CPU at 96% (>70%) - reduced to 1 thread(s)
[19/8244] PASS performance_3_system_spec.spl (499ms, 1 threads)
```

After dropping to 1 thread, it never recovers to higher parallelism even if CPU
drops back below threshold.

## Root Cause (Hypothesis)

The CPU throttle logic in the test runner:
1. Checks CPU percentage at a single point in time
2. Drops from current thread count directly to 1 (no gradual reduction)
3. Does not appear to ramp back up when CPU usage normalizes

## Status

**RESOLVED** — fixed in `src/compiler_rust/driver/src/cli/test_runner/parallel.rs`.

The runner now:
- waits for 3 consecutive high-resource samples before throttling
- reduces gradually by halving current thread count instead of jumping directly
  to the floor
- uses a default throttled floor of 4 threads instead of 1
- requires 2 consecutive low-resource samples before ramping back up
- ramps up by doubling current thread count up to the configured maximum

The CLI/config defaults and tests were updated to match the new default floor.

With 32 threads each spawning interpreter processes, CPU briefly spikes during
the initial burst. The throttle fires immediately and locks at 1 thread for the
remainder of the run.

## Expected Behavior

- Gradual reduction (e.g., 32 -> 16 -> 8 -> 4) instead of cliff to 1
- Periodic re-evaluation to ramp back up when CPU drops
- Consider hysteresis: only throttle after sustained high CPU (e.g., 3 consecutive checks)

## Workaround

Run specific test files or directories instead of the full suite:
```bash
bin/simple test test/unit/lib/nogc_async_mut/http/  # subset
bin/simple test path/to/specific_spec.spl            # single file
```

## Reproduction

```bash
bin/simple test  # Full suite, observe thread drop within first 20 tests
```
