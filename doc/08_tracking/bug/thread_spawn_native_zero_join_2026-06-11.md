# Thread Spawn Native Zero-Join Blocker

Status: Narrowed

## Summary

The original standalone native `thread_spawn` zero-join bug has been narrowed.
With a freshly rebuilt runtime/driver binary, the public host-side OS-thread
surface now works again for:

- minimal direct `thread_spawn(worker)` fork-join
- native `thread_spawn_with_args(...)` smoke
- host-native `thread_spawn(\: worker())` profile worker repro

The remaining live failure is now the Docker-compiled OS-thread profile row:
the same generated `thread_spawn(\: worker())` and fanout shapes still produce
zero-result joins when compiled inside the isolated cross-language profile
container, even when that container is pointed at the freshly rebuilt compiler
binary.

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

## Profile Impact

This is the current reason the fresh host/Docker profile rows still report:

- `Simple (native)` worker row -> `fail`
- `Simple (native)` fanout row -> `fail`

Fresh isolated profile evidence on 2026-06-11 with the stale wrapper path:

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

Fresh isolated profile evidence on 2026-06-11 with the rebuilt compiler path:

- `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`

That report still records:

- `Simple (native)` worker row -> `fail`
- `Simple (native)` fanout row -> `fail`

and the generated Docker-built binaries still reproduce:

- `build/cross_lang_perf_thread_fix_fresh/parallel_simple_native`
  -> `checksum_mismatch total=0 expected=7220643300`
- `build/cross_lang_perf_thread_fix_fresh/fanout_simple_native`
  -> `checksum_mismatch total=0 expected=1868141281000`

The remaining problem is therefore narrower than the original host/runtime bug:

- host-native rebuilt compiler path is fixed
- Docker-compiled OS-thread profile binaries still fail
- the profile report parser is not the issue

## Next Fix Target

Next target:

- isolate why Docker-compiled `thread_spawn(\: worker())` binaries still zero
  their joins when the same fresh compiler produces correct host-native output
- once Docker OS-thread rows go green, refresh the checked-in contract report
  and convert the stale native blocker evidence into regression coverage
