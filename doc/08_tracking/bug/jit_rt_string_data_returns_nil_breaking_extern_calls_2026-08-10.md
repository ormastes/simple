# jit lane: `rt_string_data(text)` evaluates to Nil, breaking every extern that takes a string pointer

- **Date:** 2026-08-10
- **Status:** OPEN — found incidentally while fixing OPEN 1 of the logging family
  sweep; deliberately not fixed there, since it is a codegen/marshal defect, not
  a logging one.
- **Lane:** `SIMPLE_EXECUTION_MODE=jit` only. The `interpreter` lane is correct.
- **Class:** engine divergence / silent extern-call failure.

## Reproduction

```
$ cat /tmp/p.spl
use std.nogc_async_mut_noalloc.log.logger as LG

fn main():
    LG.log_error("Q21_ERROR_MARK")

$ SIMPLE_EXECUTION_MODE=jit ./bin/simple run /tmp/p.spl 2>&1 1>/dev/null
[ERROR] Q21_ERROR_MARK  ERROR ... simple_compiler::interpreter_sffi: 806:
    rt_interp_call error: Runtime("rt_simpleos_log_emit: argument 2 must be an int, got Nil")
```

`SIMPLE_EXECUTION_MODE=interpreter` on the same file produces no such error.

## Analysis

`src/lib/nogc_async_mut_noalloc/log/logger.spl` calls

```
rt_simpleos_log_emit(level.to_i64(), rt_string_data(line), rt_string_len(line))
```

`rt_string_data` is declared `extern fn rt_string_data(value: text) -> i64`. In
the jit lane its result arrives at the callee as **Nil** rather than an `i64`, so
the call is rejected by the SFFI argument check. `rt_string_len` in argument 3 is
not reached.

This is not specific to logging — it will hit **any** Simple code that passes a
string's data pointer to an extern via `rt_string_data`, which is the standard
(ptr, len) marshalling idiom in the noalloc tier.

## Why it has been invisible

The failed call returns `false`, which is indistinguishable from the legitimate
hosted-stub `false` that `runtime_log_hosted.c` returns by design. The Simple side
then takes its fallthrough path and the log line is emitted anyway. The hosted
logging path therefore *works*, but for the wrong reason: it is running the
baremetal-hook-unavailable branch because the argument marshal is broken, not
because the hook is stubbed. On a jit-compiled **baremetal-hosted** build, where
`rt_simpleos_log_emit` is the real UART emitter and is *supposed* to succeed, the
same defect would silently divert every log line away from the device.

## Next step

Compare how the jit lane lowers an `extern fn (value: text) -> i64` return
against the interpreter lane; suspect the `text`-typed *argument* marshal rather
than the `i64` return, since argument 2 is the one reported Nil.

## Related

- `doc/08_tracking/bug/logging_surfaces_that_suppress_errors_by_default_family_2026-08-10.md`
  (OPEN 1 correction — where this was found)
- Runnable check that exercises the path:
  `scripts/check/check-noalloc-log-error-reaches-stderr.shs`
