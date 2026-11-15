# Native `thread.join()` returns the tagged word (1 -> Some(8))

Status: verification-pending
Found by: WebSocket lane (PR #9408), phase-1 seed `seed-vtable.exe`.

## Symptom
Native build: `thread_spawn(\: 1).join()` yielded `Some(8)`; the interpreter returns `Some(1)`.
Probe (`test/fixtures/native/thread_join_value_probe.spl`) before the fix:

```
i64_one=8
i64_42=336
args_sum=336
by_id=240
rejoin=none
```

Every value is `v << 3` — the runtime's int-tagged RuntimeValue word.

## Root cause
Both runtimes' `rt_thread_join` return the worker's result as a tagged RuntimeValue
(Rust `executor.rs` `-> RuntimeValue`; C `runtime_thread.c` returns `td->result`, the
worker's tagged return word; NIL on a repeat join). `src/lib/nogc_sync_mut/concurrent/thread.spl`
declared it `extern fn rt_thread_join(handle: i64) -> i64`, so native codegen passed the raw
word through and `join() -> i64?` wrapped it as `Some(8)`. The interpreter was unaffected
because its extern returns `Value::Int(1)` directly. Not a seed-lowering or runtime bug:
the stdlib extern declared the wrong ABI type.

## Fix
Declare `extern fn rt_thread_join(handle: i64) -> i64?`, the same shape as
`rt_channel_recv<T>(..) -> T?`, so native codegen decodes the tagged word (int -> value,
NIL -> None). No seed rebuild.

## Verification
Spec: `test/01_unit/lib/concurrent/thread_join_native_value_spec.spl` with
`THREAD_JOIN_NATIVE_BIN=build/nb/tj_probe.exe`.

## Not covered
`ThreadHandle.join()` is typed `i64?`; text/struct worker results have no typed join API
in `std.concurrent.thread`, so they are not probed here.
