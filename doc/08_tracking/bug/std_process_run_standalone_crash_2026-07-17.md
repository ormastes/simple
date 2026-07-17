# BUG: std.process.process_run crashes with "field access on nil receiver" on trivial command

- **Date:** 2026-07-17
- **Status:** open
- **Area:** standard library (std.process module wrapper around rt_process_run)
- **Severity:** high (crashes test/integration code; blocks repro of other bugs)

## Symptom

Calling `std.process.process_run` with a trivial, working command (e.g.
`/bin/echo "hello"`) crashes with:

```
runtime error: field access on nil receiver
Illegal Instruction (core dumped)
```

This occurs even outside any class method or complex context — a standalone
call in `main()` crashes immediately.

The raw underlying `extern fn rt_process_run` primitive (used directly, without
the std.process wrapper) works correctly for the same commands, suggesting the
wrapper layer has a nil-dereference bug.

## Minimal repro

```simple
use std.process.{process_run}

fn main() -> i32:
    val result = process_run("/bin/echo", ["hello"])
    print "result={result}"
    0
```

Probe: `probe06_debug_procrun.spl` (from repro session)

Expected: prints result info or runs command successfully
Actual: crashes with nil-receiver field access + SIGILL

## Workaround

Use the raw `extern fn rt_process_run` primitive directly instead of the wrapper:

```simple
extern fn rt_process_run(cmd: text, args: [text]) -> (i32, text, text):
    none

fn main() -> i32:
    val (exit_code, stdout, stderr) = rt_process_run("/bin/echo", ["hello"])
    print "exit={exit_code}"
    0
```

Verified working: `probe06_debug_rawproc.spl`

## Impact

- Blocks all test/integration code using the documented std.process API
- Blocks repro of other nested-interpreter bugs that rely on spawning subprocesses
  via the clean API (e.g., verification of `interp_method_call_result_as_arg_corruption_nested_2026-06-30`)
- Existing workaround is internal: only the raw extern is usable in practice

## Root cause (likely)

The wrapper likely attempts field access on a Result/Option value without
checking for nil or without properly destructuring. The nil receiver suggests
either a missing `Some()` unwrap or a failed struct initialization in the wrapper.

Location: `src/lib/nogc_async_mut/process.spl` (or equivalent process wrapper module)
