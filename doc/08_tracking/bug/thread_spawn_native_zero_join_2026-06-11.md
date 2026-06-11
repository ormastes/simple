# Thread Spawn Native Zero-Join Blocker

Status: Closed

## Summary

The original standalone native `thread_spawn` zero-join bug has been narrowed.
With a freshly rebuilt runtime/driver binary, the public host-side OS-thread
surface now works again for:

- minimal direct `thread_spawn(worker)` fork-join
- native `thread_spawn_with_args(...)` smoke
- host-native `thread_spawn(\: worker())` profile worker repro

The remaining Docker/profile failure from earlier in the day is closed. The
native runtime fix restored host-side `thread_spawn`, and the profile harness
was then corrected to honor explicit
`PROFILE_DOCKER_SIMPLE_BINARY=...` overrides inside the Docker container.

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

Historical checked-in blocker behavior with the stale release wrapper:

- interpreter: prints `thread_spawn_native_join_pass=true`
- SMF: prints `thread_spawn_native_join_pass=true`
- standalone native: prints `checksum_mismatch total=0 expected=14` and exits `74`

Fresh rebuilt host evidence on 2026-06-11 using
`build/cargo-target-thread-fix/debug/simple`:

- `thread_spawn_with_args_native.spl` native smoke -> pass
- `parallel.spl` host-native OS-thread worker repro -> `total = 7220643300`
- direct probe:
  - `thread_spawn_with_args(10, 32, add_pair)` -> `direct_result=42`
  - `thread_spawn_with_args(7, 11, \seed, iters: ...)` -> lambda result matches expected

## Historical Profile Impact

Before the harness fix, this was the reason the fresh host/Docker profile rows
still reported:

- `Simple (native)` worker row -> `fail`
- `Simple (native)` fanout row -> `fail`

Fresh isolated profile evidence on 2026-06-11 with the stale wrapper path:

- `doc/09_report/cross_language_perf_2026-06-11_refresh_current.md`

The generated host-side native profile binaries reproduce:

- `build/cross_lang_perf_refresh_current/parallel_simple_native`
  -> `checksum_mismatch total=0 expected=7220643300`
- `build/cross_lang_perf_refresh_current/fanout_simple_native`
  -> `checksum_mismatch total=0 expected=1868141281000`

## Closure

`thread_spawn_with_args` still has its own focused native smoke and remains a
different path, but the broad `thread_spawn` native blocker is now closed.

Fresh isolated profile evidence on 2026-06-11 with the rebuilt compiler path
after the Docker override fix:

- `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`

That report now records positive OS-thread rows:

- `Simple (native)` worker row -> `109.410 ms`
- `Simple (native)` fanout row -> `72.261 ms`

The Docker-generated binaries now execute successfully with the intended fresh
compiler binary, so the remaining gap in this lane is no longer a `thread_spawn`
correctness issue.
