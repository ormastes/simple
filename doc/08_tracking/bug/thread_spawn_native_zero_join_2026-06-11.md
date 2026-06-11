# Thread Spawn Native Zero-Join Blocker

Status: Open

## Summary

The current public `std.concurrent.thread.thread_spawn` fork-join path still
fails in standalone native artifacts. Minimal top-level worker workloads compile
successfully, run successfully in the interpreter and SMF loader, but native
joins return zeroed results and trip the checksum guard.

This is a live host/runtime blocker, not only a stale profile artifact.

## Reproduction

Focused executable evidence now lives in:

- `test/03_system/feature/usage/thread_spawn_native_zero_join_blocker_spec.spl`

The spec writes this minimal fixture:

```simple
use std.concurrent.thread.{thread_spawn, ThreadHandle}
extern fn rt_exit(code: i32)

fn worker() -> i64:
    7

fn main():
    var handles: [ThreadHandle] = []
    handles.push(thread_spawn(worker))
    handles.push(thread_spawn(worker))
    val total = handles[0].join() + handles[1].join()
    if total != 14:
        println("checksum_mismatch total={total} expected=14")
        rt_exit(74)
    print("thread_spawn_native_join_pass=true")
```

Current observed behavior with `bin/release/simple`:

- interpreter: prints `thread_spawn_native_join_pass=true`
- SMF: prints `thread_spawn_native_join_pass=true`
- standalone native: prints `checksum_mismatch total=0 expected=14` and exits `74`

## Profile Impact

This is the current reason the fresh host/Docker profile rows still report:

- `Simple (native)` worker row -> `fail`
- `Simple (native)` fanout row -> `fail`

Fresh isolated profile evidence on 2026-06-11:

- `doc/09_report/cross_language_perf_2026-06-11_refresh_current.md`

The generated host-side native profile binaries reproduce:

- `build/cross_lang_perf_refresh_current/parallel_simple_native`
  -> `checksum_mismatch total=0 expected=7220643300`
- `build/cross_lang_perf_refresh_current/fanout_simple_native`
  -> `checksum_mismatch total=0 expected=1868141281000`

## Likely Boundary

`thread_spawn_with_args` still has its own focused native smoke and remains a
different path. The active failure here is narrower:

- direct public `thread_spawn`
- top-level zero-arg worker function
- standalone native artifact
- joined results come back as zero

The problem is therefore in the native `thread_spawn` closure/function-value
execution boundary or result propagation path, not in the profile report parser.

## Next Fix Target

Fix the standalone native `thread_spawn` path so the minimal two-worker fixture
above returns `14`, then refresh the cross-language profile evidence and convert
the blocker spec into regression coverage.
