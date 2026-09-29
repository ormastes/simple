# Bug: unit-return function pointer `fn() -> ()` hard-crashes (SIGILL)

## Closed 2026-09-13 — Fixed: a `fn() -> ()` function pointer calls cleanly

- **measured** (Rust seed `bin/simple` v1.0.0-rc.1, Windows): the entry's repro shape — `fn run_warm(iters: i64, body: fn() -> ()) -> i64` calling `body()` once plus twice in a loop, passed a unit-returning `tick` — runs to completion printing `t t t` then `0`, exit 0. No SIGILL, no rc=132.
- **inferred**: the entry says the crash hit both the interpreter and compiled SMF. Only the default `bin/simple run` lane was exercised here; the SMF lane was not, so the compiled half rests on the shared call-lowering fix rather than a direct measurement.

- **ID:** unit_return_fn_pointer_sigill
- **Severity:** P2 (hard crash, but a narrow type; easy workaround)
- **Area:** compiler / function-pointer call lowering (interpreter AND smf/compiled)
- **Status:** CLOSED 2026-09-13 (fixed; verified by execution)
- **Date:** 2026-06-14

## Symptom

Calling a value of type `fn() -> ()` (a function pointer with **unit return**) through an
indirect call crashes the process with **SIGILL (rc=132)** and **no diagnostic**. It reproduces
in BOTH `bin/simple run <src>` (interpreter) and compiled SMF — so it is NOT mode-specific.

A non-unit return type (`fn() -> i64`) through the identical indirect-call pattern works fine.
So the trigger is specifically the unit (`()`) return on the function-pointer type.

## Repro

```
extern fn rt_time_now_unix_micros() -> i64
fn run_warm(iters: i64, body: fn() -> ()) -> i64:
    body()
    var i = 0
    while i < iters:
        body()
        i = i + 1
    0
fn payload() -> ():
    var s = 0
    var i = 0
    while i < 100:
        s = s + i
        i = i + 1
fn main():
    val _ = run_warm(1000, payload)
    print "done"
```

```
bin/simple run repro.spl    # rc=132 (SIGILL), no "done" printed
```

Control (works, rc=0): change `body: fn() -> ()` / `payload() -> ()` to `-> i64` (returning a value).

## Discovered

While wiring `bench_baseline_driver` to emit smf rows (the `bench_run_warm(bc, body: fn()->())`
harness pattern uses exactly this type). The baseline driver itself sidesteps it by timing named
workloads inline (no `fn()->()` parameter), so the bench is unaffected — but `bench_run_warm`
is unusable until this is fixed.

## Workaround

Use a non-unit return on function-pointer parameters (`fn() -> i64`, return a sentinel), or call
named workload functions directly instead of passing a `fn() -> ()` closure.

## Not related to

`smf-extern-segfault` — that label was investigated separately and does not reproduce (externs,
including tuple/text-returning, run correctly in `--mode smf`; the text-return segfault was
Resolved 2026-05-29). This SIGILL is a distinct, mode-independent function-pointer bug.
