# Watchdog Timeout Triage — slow_run 2026-04-27

Sources:
- `/home/ormastes/dev/pub/simple/.sstack/fix-perf-bugs/slow_run.stderr` (9042 lines)
- `/home/ormastes/dev/pub/simple/.sstack/fix-perf-bugs/slow_run.json` (62036 lines, plain test-runner output despite extension)
- `/home/ormastes/dev/pub/simple/.simple/logs/crash_3709914.log` (3 KB)

Run command: `bin/simple test --only-slow --format json --timeout 1800`

**Total watchdog kills: 25** (24 × 60s + 1 × 120s).
All 25 kills attribute to a single PID `3709914` — the parent test-runner process. Each kill produces a generic
`=== WATCHDOG CRASH === PID 3709914 / [watchdog] wall-clock timeout (Xs) exceeded` block in
`crash_3709914.log` with no spec name, no stack, no payload.

## Methodology / data quality caveat

The runner does NOT emit a per-spec banner ("RUN test/foo_spec.spl") to stderr or stdout in this
configuration. The "JSON" file is actually plain BDD-style runner output and contains exactly **one**
spec path mention (`test/feature/usage/loss_nograd_blocks_spec.spl`). All other tests appear as anonymous
description blocks. Spec attribution below is derived from **stderr proximity** — the closest preceding
file path mentioned in deprecation warnings, ERROR/WARN traces, or DEBUG markers. This is a heuristic; the
hung spec may actually be a different one running in parallel with the spec whose warnings show up nearest.

## Per-kill table (chronological, by stderr line)

| stderr line | nearest preceding spec / source mention | category | hypothesis | note |
|---|---|---|---|---|
| 1257 | (none — first kill of run) | runner / module-loader | hung | Just before kill: many `simple_compiler::interpreter::interpreter_module::module_evaluator` "Export statement references undefined symbol" WARNs. Just after: `Circular import detected, returning empty …` from `module_loader:474`. Smells like an interpreter module-load loop, not a real test workload. |
| 3169 | `test/integration/os/rv64_boot_spec.spl` (L3112) | OS / hardware | hung (probable interpreter pathology) | Immediately preceded by **14 consecutive** `DEBUG FieldAccess: self.w assignment with IN_IMMUTABLE=true` debug prints — looks like an interpreter mutability check repeating. Post-kill output is `from hir_types import {SymbolId}` (deprecated `from ... import` warnings) — different module. Likely hung loading rv64-related modules. |
| 5149 | `test/lib/std/unit/core/dsl_spec.spl` (L4780) | std-lib / DSL | hung (import storm) | Immediately preceded by ~50 lines of deprecation warnings (`Promise.new()`, `ContextBuilder.new()`, `DynamicProxy.new()`, `Pipeline.new()`, etc.) and a `dom_bridge.spl:119` namespace parse error. dsl_spec is dragging in dozens of modules through `std.unit.core` — hung in dependency graph evaluation. |
| 5629–5677 | `test/lib/std/unit/core/dsl_spec.spl` (L4780) | std-lib / DSL | **stuck in tight loop** | **24 consecutive 60s kills** within ~50 stderr lines (lines 5629, 5639, 5641, 5643, …, 5677 — almost back-to-back). Surrounding output: `src/os/kernel/ipc/syscall.spl:1515 legacy inline asm syntax` warnings, ERROR `Failed to parse module` messages from `module_loader:519`. Watchdog fires, prints crash, but parser/loader is wedged and immediately re-trips the watchdog. This single hung dsl_spec import session accounts for ~24/25 of all kills. |
| 9041 | `test/system/llm/llm_math_system_spec.spl` (L9032) | LLM / system | unknown — possibly genuine-slow OR unsupported FFI | 120s timeout (longest). Immediately preceded on stderr by `error: rt_cli_watch_file is not supported in interpreter mode`. The spec uses `import std.spec` (deprecated). After the unsupported-FFI error, the spec ran for 120s before kill — consistent with a polling/wait loop calling the unsupported builtin. |

## Grouped by category

### compiler / runner internals (1 kill)
- `[unattributed early-load]` line 1257 — module-loader circular-import path; `rt_cli_watch_file`-style scenario or first-spec init hang.

### OS / hardware integration (1 kill)
- `test/integration/os/rv64_boot_spec.spl` :: (unknown `it`) — hung; surrounded by `IN_IMMUTABLE` interpreter loops; classify hung. (rv64_boot is plausibly genuine-slow if it spins up QEMU, but the immediate-prior signal is the interpreter loop, not boot output.)

### std-lib DSL (1 spec, 25 kills total: 1 + 24 cluster) — DOMINANT CATEGORY
- `test/lib/std/unit/core/dsl_spec.spl` :: (unknown `it`) — hung in import / module-load. This single spec accounts for ~96 % of the watchdog signal in the run (kill at 5149 plus the 24-kill cluster 5629–5677). Loader is repeatedly logging `Failed to parse module` and tripping the 60 s wall-clock over and over.

### LLM / system (1 kill)
- `test/system/llm/llm_math_system_spec.spl` :: (unknown `it`) — 120s, after `rt_cli_watch_file is not supported in interpreter mode`. Hypothesis: spec retries / waits on the unsupported FFI.

## Top 3 hot categories

1. **std-lib DSL (`dsl_spec.spl`)** — 25 kills (24 cluster + 1 setup). One spec, repeated re-trip.
2. **runner / module-loader early init** — 1 kill (circular-import territory).
3. **OS rv64_boot integration** — 1 kill.
4. **LLM math system** — 1 × 120s kill.

(The "32 distinct spec files" figure from stderr is mostly deprecation warnings emitted by transitive
imports; it does not mean 32 specs ran.)

## Executive summary

Out of 25 watchdog kills in this `--only-slow` run, the overwhelming majority (24) are a tight cluster of
re-trips inside one stuck spec — `test/lib/std/unit/core/dsl_spec.spl` — in the interpreter module loader.
The loader is stuck in a parse / import loop (`module_loader:519 Failed to parse module` repeating, mixed
with `kernel/ipc/syscall.spl` deprecation noise from transitively-loaded modules), and each 60 s the watchdog
fires, prints the crash banner, and the loader immediately keeps spinning to trip again. The four remaining
kills cluster around: a first-spec circular-import condition (line 1257), `rv64_boot_spec` blocked behind a
`self.w` `IN_IMMUTABLE` mutability-check loop (line 3169), and `llm_math_system_spec` spending its full 120 s
budget after hitting `rt_cli_watch_file is not supported in interpreter mode` (line 9041). **Bottom line: this
run is not a perf signal across many specs — it is one wedged spec (dsl_spec) plus three single hangs
attributable to interpreter limitations (mutability path, unsupported FFI, circular import), not to genuine
slow workloads.**

## Recommended next-level diagnostics

The current stderr lacks per-spec banners, so spec attribution is heuristic. To turn this into actionable
per-spec / per-`it` triage, re-run with one of:

- `bin/simple test --only-slow --list` — emit the spec ordering without running, then map by index.
- `bin/simple test --only-slow --format text --verbose` (or whatever verbosity flag the runner exposes) so
  each spec emits a `RUN <path>` banner before execution. The `--format json` mode used here apparently
  suppresses the banners.
- Run dsl_spec in isolation with a short timeout to confirm the wedge:
  `bin/simple test test/lib/std/unit/core/dsl_spec.spl --timeout 30` and inspect with strace / py-spy.
- For the line-1257 first-kill, instrument or temporarily lower the watchdog to capture which spec the
  worker had just dequeued (no `WORKER N: starting <spec>` markers exist in the current stderr).
- Per-PID crash logs would be much more useful if the watchdog wrote the spec path it was monitoring at the
  moment of fire — file as a runner enhancement (`crash_<pid>.log` should include `spec=…`, `it=…`).
