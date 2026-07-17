# Importing `app.io.mod` under the interpreter crashes with a stack overflow

**Date:** 2026-07-17
**Severity:** high (silently corrupts any BDD spec that imports the facade)
**Status:** open

## Symptom

Any `.spl` file that imports anything from `app.io.mod` — even a single
non-process helper like `file_exists` — aborts with:

```
fatal runtime error: stack overflow, aborting
```

when executed under the interpreter (`SIMPLE_RUNTIME_MODE=interpreter`, the
mode `simple test <file> --no-session-daemon` forces; also reproduces via a
plain `simple run <file>` on the current seed,
`src/compiler_rust/target/release/simple`).

Repro (minimal):

```
use std.spec.*
use app.io.mod.{file_exists}

describe "repro":
    it "just calls file_exists from app.io.mod":
        expect(file_exists("/etc/hostname")).to_equal(true)
```

```
$ src/compiler_rust/target/release/simple test /tmp/repro.spl --no-session-daemon
...
fatal runtime error: stack overflow, aborting
error: test-runner: no examples executed
FAIL /tmp/repro.spl
```

The crash point is nondeterministic relative to the spec's own `it` bodies:
in some specs it happens before any example runs (reported as `Passed: 0,
Failed: 1`, "no examples executed"); in a spec with multiple `it` blocks that
each import-and-call `app.io.mod` functions, all `it` bodies can print their
own `✓`/`N examples, 0 failures` cleanly and the crash still happens
afterward (module teardown?), corrupting the process exit code and making the
wrapper report `error: test-runner: spec failed` despite a clean internal
BDD summary.

## Isolation

- `use std.io_runtime.process_run` (or any other function from
  `std.io_runtime`) — **does not** crash; confirmed via the same repro shape.
- `use app.io.mod.{process_run}` / `{process_run_timeout}` / `{file_exists}`
  — **all** crash, including calls that never spawn a subprocess. This rules
  out the process-spawn path specifically; the overflow appears tied to
  importing/initializing the `app.io.mod` module itself under the
  interpreter, not to any one function in it.
- `std.io_runtime` is a leaf module of plain `extern fn` wrappers.
  `app.io.mod` has a much larger transitive import surface (re-exports of
  `cli_run_*` dispatch helpers, logging, math, etc. — see
  `src/app/io/mod.spl`), which is the likely site of a circular or
  self-referential import that the interpreter's module loader resolves via
  unbounded recursion.

## Impact

Any test spec that follows the documented convention of importing
`app.io.mod` for process/file helpers (widely used across
`test/03_system/gui/*_spec.spl` and others) crashes under interpreter mode.
Those existing specs apparently do not hit this in practice only because they
are not run through this exact `--no-session-daemon` / plain `run` path in a
way that was checked here — this needs a broader sweep to know how many
specs are actually affected today.

## Workaround (used in `test_runner_contract_system_spec.spl`)

Use `std.io_runtime.{process_run, file_read, file_write, file_exists,
dir_create_all}` instead of `app.io.mod`. For a bounded-timeout invocation
without `app.io.mod.process_run_timeout`, wrap the command with the `timeout`
shell utility and drive it through `std.io_runtime.process_run`:

```
process_run("/bin/sh", ["-c", "timeout 60 " + seed_binary + " test --no-session-daemon " + target])
```

## Fix direction

- Reproduce under a debugger/backtrace to find the recursive module-init
  call in `app.io.mod`'s import graph (likely a re-export cycle through one
  of the `cli_run_*` helpers).
- Add a regression spec that imports `app.io.mod` under interpreter mode and
  asserts a real function call succeeds (currently would fail/crash; do not
  add as passing coverage until the underlying loader bug is fixed).

## How found

2026-07-17, while writing a `test/03_system/app/test_runner` SSpec system
test that drives the real seed binary via `process_run_timeout` from
`app.io.mod`, per repo convention seen in several `test/03_system/gui/*_spec.spl`
files. The spec's own examples reported clean (`N examples, 0 failures`) but
the wrapper still reported `error: test-runner: spec failed`; the actual
cause was this stack overflow at/after module use, not a real example
failure.
