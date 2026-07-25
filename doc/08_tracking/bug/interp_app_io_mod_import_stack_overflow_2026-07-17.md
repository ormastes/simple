# Importing `app.io.mod` under the interpreter crashes with a stack overflow

**Date:** 2026-07-17
**Severity:** high (silently corrupts any BDD spec that imports the facade)
**Status:** RESOLVED 2026-07-17 (see Resolution below)

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

## Resolution (2026-07-17)

**This was not a module-loader import cycle.** `gdb` backtraces on the
minimal repro (`src/compiler_rust/target/release/simple run`) showed the
native stack exhausted inside a repeating
`evaluate_call -> eval_call_expr -> evaluate_expr ->
handle_method_call_with_self_update -> exec_block_fn ->
execute_function_body -> exec_function*` chain — a runtime **function-call**
cycle, not module-load recursion. `module_cache.rs` / `module_evaluator.rs`
already have correct, working circular-import detection
(`MODULES_LOADING`/`MAX_MODULE_DEPTH`/partial-exports-on-cycle) and were not
at fault; both files were unmodified (verified clean against `origin/main`
before and after this investigation).

### Root cause 1 — self-shadowing import in `fs_helpers.spl`

`src/compiler_rust/lib/std/src/io/fs_helpers.spl` (a stdlib copy bundled
with the Rust seed, transitively reachable from `app.io.mod` via
`app.io.cli_ops` -> ... -> `infra.file_io`) had:

```
use infra.file_io.{read_file, write_file, create_dir_all, file_exists, remove_file, list_dir}
...
pub fn exists(path: text) -> bool:
    file_exists(path)          # intended: the imported infra.file_io.file_exists

pub fn file_exists(path: text) -> bool:
    """Compatibility alias for the exported helper name."""
    exists(path)                # calls exists(), which calls file_exists() again
```

The local `pub fn file_exists` (added later as a "compatibility alias")
shares its name with the imported `file_exists`. Once loaded, this makes
`exists()`'s unqualified call to `file_exists(...)` resolve back to the
local alias instead of the import, and `exists()`/`file_exists()` call each
other forever — unconditional infinite mutual recursion, independent of any
overload-resolution nuance.

The interpreter's function registry (`FUNCTION_OVERLOADS` in
`interpreter_state.rs`) is process-wide and keyed by bare name, not scoped
per module. `app.io.mod`'s large transitive import surface (via
`app.io.cli_ops`'s `context_generate`/`context_stats`/... helpers) is what
pulls `fs_helpers.spl` into the loaded-module graph at all; once loaded, its
broken `file_exists` candidate pollutes global name resolution for **any**
unqualified `file_exists` call anywhere in the process (confirmed via
`SIMPLE_DEBUG_OVERLOAD_SELECT=1` trace: `[module-tie] fn=file_exists
current=...fs_helpers.spl owner=...fs_helpers.spl`). This is why the crash
reproduced for `file_exists`, `process_run`, and `process_run_timeout`
alike (all three variants from the Isolation section above were re-tested
and now pass) — the specific symbol the user imports doesn't matter once
`app.io.mod`'s surface is loaded.

**Fix:** `fs_helpers.spl`'s `exists`/`file_exists`/`exist` now call a
locally-declared `extern fn rt_file_exists(path: text) -> bool` directly,
instead of routing through the shadowed import. No more name collision, no
more cycle. (`src/lib/` — the pure-Simple self-hosted stdlib — has no
`fs_helpers.spl`, so this defect and fix are confined to the Rust seed's
bundled copy; a repo-wide scan for the same `import name == local fn name`
shape in `src/compiler_rust/lib/std/` found two more matches, in
`spec/error_handling.spl` and `tooling/dashboard/notify.spl`. Both call the
fully-qualified `core.time.now_iso8601()` inside the shadowing function
rather than the bare name — **unverified assumption**: this is presumed
safe from the same unqualified-resolution trap because it doesn't go
through the ambiguous bare-name lookup path, but this was not traced
through the interpreter to confirm; left as-is, flagged here for anyone
who later sees a similar hang near either file.)

### Root cause 2 — diagnose-not-crash safety net was off by default in release

Even with root cause 1 fixed, *any* genuine interpreter-level infinite
recursion (a bug just like this one, elsewhere) would still raw
stack-overflow-crash the process instead of producing a clean diagnostic.
The interpreter already has a generic recursion-depth guard
(`push_call_depth` / `RECURSION_DEPTH` / `MAX_RECURSION_DEPTH=1000` in
`interpreter_state.rs`, backed by `simple_common::fault_detection`), wired
into `execute_function_body` on every interpreted function call. It was
never the module loader that was missing cycle detection — it was this
call-level guard being **compiled disabled by default in release builds**
(`STACK_OVERFLOW_DETECTION_ENABLED = AtomicBool::new(false)` under
`#[cfg(not(debug_assertions))]` in `src/compiler_rust/common/src/fault_detection.rs`).
Debug builds defaulted it to `true` and always had the safety net; release
builds — which is what `src/compiler_rust/target/release/simple` (used by
`simple run` / most `simple test` invocations) is — did not.

Verified empirically: running the original repro with
`SIMPLE_STACK_OVERFLOW_DETECTION=1` (before the `fs_helpers.spl` fix)
converted the raw crash into a clean `semantic: function 'exists' not
found` interpreter error — same underlying cycle, no crash. 1000 levels of
interpreter recursion also comfortably fits inside the 64MB `simple-main`
thread stack (`driver/src/main.rs` `DESIRED_STACK`), so the limit is not
starved against the stack budget.

**Fix:** `STACK_OVERFLOW_DETECTION_ENABLED` now defaults to `true`
unconditionally (both debug and release). `SIMPLE_STACK_OVERFLOW_DETECTION=0`
/ `set_stack_overflow_detection_enabled(false)` remain available as an
opt-out escape hatch. Rebuilt `src/compiler_rust/target/release/simple` and
verified with **no env var** that a synthetic mutual-recursion fixture
(`ping()`/`pong()` calling each other via `describe`/`it`) now produces
`stack overflow: recursion depth 1000 exceeded limit 1000 in function
'ping'` instead of aborting.

### Files changed

- `src/compiler_rust/lib/std/src/io/fs_helpers.spl` — break the self-shadow
  cycle (root cause 1).
- `src/compiler_rust/common/src/fault_detection.rs` — default
  `STACK_OVERFLOW_DETECTION_ENABLED` to `true` in release builds too, with
  rationale comment (root cause 2, defense-in-depth).
- `src/compiler_rust/driver/tests/interpreter_bdd.rs` — two new regression
  tests: `mutual_recursion_diagnoses_cleanly_instead_of_crashing` (generic
  safety-net proof, independent of `fs_helpers.spl`) and
  `app_io_mod_import_no_longer_stack_overflows` (exact repro from this doc).
  Both pass; full `interpreter_bdd.rs` suite (6 tests) green, no
  regressions. `simple-common::fault_detection` unit tests (5) and
  `interpreter_state` recursion-guard unit tests (7) also verified green
  after the default flip.
- `module_cache.rs` / `interpreter_module/module_evaluator*.rs` —
  **unmodified**; confirmed not implicated (see above) and confirmed clean
  against `origin/main` throughout.

### Known separate, pre-existing issue (not fixed here, out of scope)

The `simple` CLI's wrapper-level exit-code accounting disagrees with a
clean BDD summary specifically for specs that import `app.io.mod`: `simple
run`/`simple test` can print `N examples, 0 failures` and still exit 1 /
report `error: test-runner: spec failed`. This is what the "How found"
paragraph above originally (and reasonably) attributed to this crash, but
it reproduces independently of the stack overflow — confirmed both before
and after the fixes above, and confirmed via full-log grep that no
crash/panic/SIGSEGV text is present when it happens. It lives in
`src/app/test_runner_new/test_runner_single.spl` (also matched by
`src/lib/nogc_sync_mut/test_runner/test_result_wrapper.spl`), which is
explicitly out of scope for this fix (foreign no-touch for this
investigation). Recommend filing as its own bug if not already tracked.

### Import-pattern guidance

Per repo convention (`.claude/memory` note: "Test imports should use
`std.io_runtime` not `app.io`"), specs that only need
process/file/dir helpers should prefer `std.io_runtime` — it is a leaf
module of plain `extern fn` wrappers and was never implicated in this bug.
`app.io.mod` remains usable now that the underlying interpreter cycle is
fixed, but its much larger transitive surface (via `app.io.cli_ops`) is
inherently more exposed to this class of process-wide name-collision bug
than a narrow leaf import.
