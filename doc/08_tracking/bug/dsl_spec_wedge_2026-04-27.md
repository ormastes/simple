# dsl_spec wedge — misattributed; runner observability bug + dsl.spl semantic failures (2026-04-27)

## TL;DR

The triage report `.sstack/fix-perf-bugs/timeout_triage.md` attributed 24/25
watchdog kills in the `--only-slow` run to a single wedged spec
(`test/lib/std/unit/core/dsl_spec.spl`). **That attribution is wrong.** In
isolation the spec completes in **235 ms** with 6 deterministic semantic
failures — there is no parser/loader hang, no wedge, no retry loop.

The real findings are two unrelated bugs:

1. **Runner observability bug** — the test runner reuses one parent PID for all
   sequentially-run specs and the watchdog's crash log appends to a single
   per-PID file. A run with N slow specs that each trip the per-test timeout
   produces N `=== WATCHDOG CRASH ===` blocks in one file with no spec path
   recorded. Triage was forced to guess "which spec" by stderr proximity, and
   the heuristic happened to point at dsl_spec because dsl_spec emits a burst
   of deprecation warnings just before an unrelated cluster of slow specs ran.
2. **dsl.spl semantic regressions** (separate, real, but fast — not a wedge) —
   `src/compiler_rust/lib/std/src/core/dsl.spl` has six deterministic
   `it`-block failures: 4× `cannot modify self in immutable fn method` (mutable
   field assignment without a `mut self` declaration / interpreter
   `IN_IMMUTABLE` false-positive) and 2× constructor arity mismatch
   (`function expects N argument(s), but more were provided` on
   `DynamicProxy(handler)` / `QueryBuilder()`). These are visible bugs but they
   complete in ~200 ms — they cannot have produced the 24-kill cluster.

## Symptom

`bin/simple test --only-slow --format json --timeout 1800` produces
`crash_<parent-pid>.log` containing 25 `=== WATCHDOG CRASH ===` blocks
(24 × 60 s wall-clock + 1 × 120 s) appended to a single file with no spec
attribution. The triage report concluded — heuristically — that this was one
wedged spec re-tripping the watchdog, and pointed at
`test/lib/std/unit/core/dsl_spec.spl` based on the closest preceding stderr
mention.

## Reproduction

Isolation repro (proves dsl_spec is NOT wedged):

```bash
timeout 90 bin/simple test test/lib/std/unit/core/dsl_spec.spl 2>&1 | tail -60
```

Output (verbatim, trimmed):

```
Running: test/lib/std/unit/core/dsl_spec.spl
Context blocks
warning: ContextBuilder.new() is deprecated, use ContextBuilder() instead
DEBUG: cannot modify self in file: test/lib/std/unit/core/dsl_spec.spl, ...
  ✗ provides context-aware building
    semantic: cannot modify self in immutable fn method
... (6 failures total)
  FAILED (201ms)
═══════════════════════════════════════════════════════════════
Test Summary
Files: 1   Passed: 0   Failed: 6   Duration: 235ms
✗ Some tests failed
Slowest tests:
       201ms  test/lib/std/unit/core/dsl_spec.spl
```

235 ms total, 6 deterministic failures, zero hang.

## Root cause

### Root cause class: **runner observability bug + misattributed triage** (NOT module-loader bug, NOT parser bug, NOT stale spec, NOT circular import)

Verified evidence:

1. **`src/compiler_rust/compiler/src/interpreter_module/module_loader.rs:519`**
   — the "Failed to parse module" log line is emitted **once per parse
   failure**, immediately followed by `unmark_module_loading`,
   `decrement_load_depth`, and a clean `Err(CompileError::Parse(...))` return
   (lines 514–525). It is **not** wrapped in any retry loop. Multiple
   "Failed to parse module" lines in stderr therefore correspond to multiple
   distinct failed module loads, not a retry on the same module.
2. **`src/compiler_rust/driver/src/cli/test_runner/execution.rs:445–474`** —
   tests run **sequentially in the same parent process**. Each spec gets a
   fresh `start_watchdog(per_test_timeout_secs(path))` (line 450) followed by
   `stop_watchdog()` + `reset_timeout()` (lines 473–474). When a spec's
   per-test deadline fires, the watchdog thread (`watchdog.rs:84–89`) calls
   `write_watchdog_crash_log()` and `return`s. The next spec's
   `start_watchdog` then resets `TIMEOUT_EXCEEDED=false` and starts a fresh
   60 s deadline.
3. **`src/compiler_rust/compiler/src/watchdog.rs:117–141`** —
   `write_watchdog_crash_log()` opens
   `.simple/logs/crash_<process::id()>.log` with
   `OpenOptions::new().create(true).append(true)`. **All N watchdog firings in
   the lifetime of one parent process append to one file with no spec path,
   no `it` name, no module path** — only `PID`, `OS`, and the timeout-exceeded
   message.

So 25 `=== WATCHDOG CRASH ===` blocks under one PID = **25 different specs
each timing out**, not one spec timing out 25 times. The triage report's own
methodology section (`## Methodology / data quality caveat`) explicitly warns
that spec attribution is heuristic via stderr proximity and "the hung spec may
actually be a different one"; this bug doc confirms that caveat applied.

### Why dsl_spec was the false positive

dsl_spec imports `std.core.dsl` (`src/compiler_rust/lib/std/src/core/dsl.spl`),
which transitively triggers a burst of `Promise.new()`,
`ContextBuilder.new()`, `DynamicProxy.new()`, `Pipeline.new()`,
`AttributeDict.new()`, `QueryBuilder.new()` deprecation warnings. That burst
landed in stderr near the 24-kill cluster (lines 5629–5677), but dsl_spec
itself completed in 235 ms and the cluster came from a different group of
genuinely-slow specs that the runner did not banner.

### Secondary finding — dsl.spl semantic failures (separate bug)

In isolation `dsl_spec.spl` reports 6/6 failures, all deterministic:

| `it` block | error |
|---|---|
| `Context blocks › provides context-aware building` | `semantic: cannot modify self in immutable fn method` (`self.data[...]` assignment, file `test/lib/std/unit/core/dsl_spec.spl`) |
| `Method missing › handles undefined methods` | `semantic: function expects 2 argument(s), but more were provided` (`DynamicProxy(handler)`) |
| `Method missing › enables dynamic proxies` | same arity mismatch |
| `Method missing › supports attribute dictionaries` | same arity mismatch on `AttributeDict()` |
| `Fluent interfaces › enables method chaining` | `function expects 1 argument(s), but more were provided` (`QueryBuilder()`) |
| `Fluent interfaces › supports pipeline transformations` | `cannot modify self.data in immutable fn method` (`DEBUG FieldAccess: self.data assignment with IN_IMMUTABLE=true`) |

The `IN_IMMUTABLE=true` debug print is the same interpreter mutability-checker
pattern that the triage report flagged for `rv64_boot_spec` (`self.w
assignment with IN_IMMUTABLE=true`). It is a recurring class — likely an
interpreter false positive on `__init__`-style field initialization, or
`dsl.spl` is missing `mut self` on its setter methods. Either way, it is fast
and visible — not a wedge.

## Proposed fix

Two separate fixes; neither touches the interpreter module loader (which the
task explicitly asked us not to risk).

### Fix 1 — runner observability (real fix for the misattribution)

**File:** `src/compiler_rust/driver/src/cli/test_runner/execution.rs:450`

Pass the spec `path` (and ideally the current `it` name, when available) into
the watchdog so the crash log can attribute the timeout. Concrete shape:

```rust
// Was:
start_watchdog(timeout_secs);
// Should be:
start_watchdog_with_context(timeout_secs, path.to_path_buf());
```

And in `src/compiler_rust/compiler/src/watchdog.rs:117–141`, change
`write_watchdog_crash_log(msg)` to also write `spec=<path>` and (if available)
`it=<name>` lines. The existing `=== WATCHDOG CRASH ===` block format already
has space for it; no log-parser changes elsewhere needed.

Also recommended: emit a `RUN <path>` banner on stderr before each spec
executes (the runner already prints `Running: <path>` in single-file mode but
suppresses it in `--format json` batch mode). This was the next-level
diagnostic the triage report itself recommended.

### Fix 2 — dsl.spl semantic regressions (separate bug)

**File:** `src/compiler_rust/lib/std/src/core/dsl.spl` (694 lines, last
touched in `bbd1a4090f resolve ui_access_protocol main conflicts`).

Two sub-fixes, both **needs further investigation** to decide between two
plausible causes:

- `cannot modify self in immutable fn method` on `self.data[...] =`: either
  add `mut self` annotation to `set` / `add` / setter methods on
  `ContextBuilder`, `Pipeline`, `AttributeDict`, OR fix the interpreter's
  `IN_IMMUTABLE` checker to allow field assignment inside `__init__` /
  declared-mutating methods. Recommend a separate triage to pick.
- `function expects N argument(s), but more were provided` on `DynamicProxy(handler)`,
  `QueryBuilder()`, `AttributeDict()`: the
  `<Class>.new() is deprecated, use <Class>() instead` rewrite path appears to
  be passing implicit-self plus the user args, double-counting `self`.
  Investigate `__init__` arity in the constructor-rewrite shim — likely
  located near the deprecation-warning emitter.

## Workaround

**Do NOT add `# @disabled` to `dsl_spec.spl`.** Per advisor review:

1. dsl_spec is not the wedged spec — disabling it will NOT stop the watchdog
   kills, because dsl_spec is not what trips them.
2. Disabling it would silence 6 real semantic-error failures unrelated to the
   wedge (Fix 2 above).

**Actual workaround for the perf-bugs run:** rerun `--only-slow` with a
verbose mode that emits per-spec banners and re-triage from there. Per the
existing triage report's own recommendations:

```bash
bin/simple test --only-slow --list                    # emits spec ordering
bin/simple test --only-slow --format text --verbose   # per-spec RUN banners
```

Then map the 24 watchdog-fire timestamps to the spec running at each
timestamp. Likely candidates from the existing triage already-flagged stderr
adjacencies: `test/integration/os/rv64_boot_spec.spl`,
`test/system/llm/llm_math_system_spec.spl`, and other genuine-slow specs in
the `--only-slow` filter set.

## Cross-references

- Triage report: `.sstack/fix-perf-bugs/timeout_triage.md`
- Latest crash log: `.simple/logs/crash_168469.log` (PID 168469, today)
- Loader source: `src/compiler_rust/compiler/src/interpreter_module/module_loader.rs:519`
- Watchdog source: `src/compiler_rust/compiler/src/watchdog.rs:64–141`
- Test execution loop: `src/compiler_rust/driver/src/cli/test_runner/execution.rs:445–474`
- DSL module: `src/compiler_rust/lib/std/src/core/dsl.spl`
- Spec under test: `test/lib/std/unit/core/dsl_spec.spl`

## Status

- Bug doc only. **No source changes applied.** Both fixes touch perf-sensitive
  / system-wide code paths (test-runner watchdog, std-lib core module) and
  warrant explicit user direction before edit.
