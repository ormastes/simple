# `simple test` child binary still ignores the invoking binary — a rebuilt seed silently tests with the stale deployed one

- **ID:** simple_test_child_binary_ignores_invoking_binary_recurrence_2026-08-08
- **Status:** OPEN (recurrence)
- **Severity:** high (measurement trap — a verified-looking fix run is executed
  by a binary that does not contain the fix)
- **Date:** 2026-08-08
- **Prior:** `test_runner_child_binary_ignores_invoking_binary_2026-07-27.md`

## Symptom

Running a spec with a freshly rebuilt compiler:

```
$ src/compiler_rust/target/release/simple test test/unit/lib/zz_ann_probe_spec.spl
...
child binary: /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple
error: semantic: variable `noalloc` not found
Results: 1 total, 0 passed, 1 failed
```

The spec is executed by the **stale deployed** binary, not the invoking one, so
the run reports the pre-fix behaviour and looks like "the fix did not work".
With `SIMPLE_BINARY` pointed at the same rebuilt binary, the identical spec
passes 1/1.

## Why the existing guard did not hold

`find_simple_binary()` (`src/app/test_runner_new/test_runner_single.spl:158`)
is supposed to resolve the invoking binary in-process via
`rt_path_absolute("/proc/self/exe")` precisely to avoid this. In this
configuration that step did not yield the invoking binary and resolution fell
through to `bin/simple`. The 2026-07-27 fix is therefore not covering the
"run a non-deployed binary directly" case.

## Impact

Anyone who rebuilds the seed to verify a compiler fix and then runs
`<rebuilt> test <spec>` gets a **silently stale** result. This is the same class
of trap as the `bin/simple run` script-directory stdlib resolution finding
(which invalidated a 4-row table cited as authoritative four times).

## Workaround until fixed

Always set `SIMPLE_BINARY=<abs path to the binary under test>` when verifying a
compiler change with `test`, and **read the `child binary:` line** — the runner
already prints it. Treat a `child binary:` that is not the binary you built as
a void measurement.

## Fix direction

Either make the `/proc/self/exe` resolution actually authoritative on this path,
or make the runner refuse to run when the resolved child binary differs from the
invoking process and `SIMPLE_BINARY` was not set explicitly (fail closed with a
message naming both paths).
