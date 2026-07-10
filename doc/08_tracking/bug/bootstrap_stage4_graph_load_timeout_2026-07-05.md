---
id: bootstrap_stage4_graph_load_timeout_2026-07-05
status: OPEN
severity: high
discovered: 2026-07-05
discovered_by: Stage-4 bootstrap execution on Apple M4
related: scripts/bootstrap/bootstrap-from-scratch.sh
related: build/bootstrap/logs/aarch64-apple-darwin/stage4-native-build.log
---

# Stage-4 Bootstrap: Native-build graph loading exceeds default 7200s timeout

## Summary

Stage-4 bootstrap's interpreted native-build worker exceeded the default 7200-second (2-hour) timeout on Apple M4. The module graph loading phase alone consumed approximately 97 minutes before reaching parse/compile phases, indicating a severe performance bottleneck in dependency resolution and module discovery.

## Evidence

- Platform: Apple M4 (aarch64-apple-darwin)
- Build stage: Stage 4 (pure-Simple self-hosted)
- Phase that timed out: Module graph loading
- Time spent in graph loading: ~97 minutes (before parse/compile)
- Default timeout: 7200 seconds
- Log location: `build/bootstrap/logs/aarch64-apple-darwin/stage4-native-build.log`

## Impact

Stage-4 bootstrap remains incomplete and cannot produce a fresh pure-Simple binary. The long timeout blocks verification builds and prevents rapid iteration on bootstrap fixes.

## Linux confirmation 2026-07-10

The same interpreted-worker bottleneck blocks the full-size CPU-SIMD exporter
on x86_64 Linux. A patched debug bootstrap passed strict stub validation, then
timed out before codegen/output at both `--timeout 120` and `--timeout 600` while
loading/parsing the reachable `src/app` + `src/lib` closure. No exporter binary
was produced. This confirms the blocker is not Apple-only and must be removed
before a fresh retained 4K/8K CPU-SIMD/Cairo comparison can be accepted.

## Scope

The issue is in the module graph loading phase (`compiler/99.loader/module_graph.spl` or similar), likely:
- Quadratic or worse complexity in dependency resolution
- Redundant graph traversals
- Missing memoization or caching of module metadata
- Inefficient file I/O during discovery

`bootstrap-from-scratch.sh:430` currently passes no `--timeout` argument, so the native-build worker uses a hardcoded default that is insufficient for the current graph-loading performance.

## Next Steps

1. Profile the native-build module graph loading phase to identify the bottleneck (dependency resolution, disk I/O, algorithm complexity).
2. Add memoization/caching for module metadata queries.
3. Either fix the underlying performance issue or add a configurable `--timeout` parameter to `bootstrap-from-scratch.sh` with a reasonable default for typical hardware (e.g., 14400+ seconds for interpreted stage-4).

## Status update 2026-07-06

The error message's recommended fix — "use the in-process backend for cross-target builds" — was tried and does NOT help for the full-CLI stage-4 build on Apple M4. Running the stage-4 build via the in-process path (deployed self-hosted `bin/simple native-build --backend llvm-lib --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/cli/main.spl`, WITHOUT `SIMPLE_BOOTSTRAP`/`--timeout` so `native_build_main.spl` dispatches straight to `cli_native_build` in-process instead of spawning the interpreted worker) was left running for ~91 minutes and STILL had not reached codegen:

- No output binary was produced (`build/bootstrap/full/aarch64-apple-darwin-macho/simple` never appeared).
- At 91 min the process was still in the parse / HIR-lowering phase, emitting `[parser_error]` lines against core compiler sources (`src/compiler/mir_opt/mir_opt/pattern_dispatch.spl`, `src/compiler/hir/hir_lowering/_Items/declaration_lowering.spl`, `src/compiler/tools/fix/rules/impl_/lint_code.spl`, `src/std/nogc_sync_mut/env/variables.spl`). Graph-load + full-source parse is the bottleneck; the in-process path shares it because it still loads and parses the entire import graph before any codegen.
- Conclusion: switching interpreted-worker → in-process does NOT bypass the graph-load/parse cost for the full-CLI source set. The real fixes remain the profiling/memoization items above (and/or a self-hosted-parser investigation into why so many core files raise parser errors under this build path).

Consequence for the `browser` subcommand: the currently deployed binary `bin/release/aarch64-apple-darwin-macho/simple` (Jul 5 14:16) predates the `browser` subcommand wiring, so `bin/simple browser --help` still returns `error: file not found: browser`. No rebuild could be produced within budget, so the binary was left untouched (backup NOT taken, nothing deployed — deploy stayed clean).

Working fallback for users TODAY (Approach C, verified on the deployed binary): the browser app entry is runnable directly as a file —
`bin/simple src/app/ui.browser/main.spl <file.ui.sdn> --open` (dispatches, `--help`/`--open`/`--dry-run` all work). The `browser` and `ui.browser` bare subcommands do NOT dispatch on this binary; only the direct-file path does.

## ROOT-CAUSE INVESTIGATION 2026-07-06 (Opus, controlled measurement)

Profiled the parse/load phase on controlled growing subsets (each probe ≤300s;
never ran the full 90-min build). Added a timestamped phase profiler to the
driver (`SIMPLE_COMPILER_PHASE_PROFILE=1`, commit "timestamped phase profiler")
and used it for the per-phase / per-file numbers below.

### 1. Hot phase — PHASE 2 PARSE, running INTERPRETED (the whole finding)

For the 6-file `src/app/context/main.spl` closure (build runs to completion):

| phase | wall |
|-------|------|
| phase1 load_sources | **1 ms** |
| **phase2 parse (`parse_all_impl` → `parse_full_frontend`)** | **41,206 ms** |
| phase3 lower_and_check (HIR + resolve + const-fold) | **746 ms** |

Per-file parse cost is LINEAR in source size at ~**0.8 ms/char**, e.g.
`context_ops.spl` 16,131 chars → 12.8s; `sqlite_sffi.spl` 14,050 → 10.1s;
`io_runtime.spl` 834 → 0.47s. Sub-step split inside `parse_full_frontend`:
`preprocess_conditionals`+desugar ≈ 0.5%, `parse_and_build_module` (lex + core
parser bridge) ≈ **99%**. So there is NO redundant re-parse, NO O(n²) graph
work, NO import-resolution blowup — the wall is simply the hand-written frontend
lexer/parser executing in the INTERPRETER.

Hot loop: `src/compiler/80.driver/driver.spl:355` (parse loop) →
`src/compiler/10.frontend/frontend.spl:34` `parse_full_frontend` →
`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:455`
`parse_and_build_module`.

WHY interpreted: `simple native-build` dispatches via
`src/app/cli/dispatch.spl:99` `cli_run_file(...)`, i.e. the whole compiler
driver is INTERPRETED from source, not the compiled driver linked into the
binary. `check`/all subcommands share this. (`native_build_main.spl` was
concurrently rewritten to be worker-only; the worker also runs interpreted.)

### 2. Scaling curve (interpreted native-build, --entry-closure)

closure=1(hello) 22s · closure=12(sj) 61s · closure=6(context) 96s ·
closure=16(ui_build) 213s · closure=36(sim) >300s(timeout). The x-axis is
module **count** but the real driver is total **chars** (heavier modules cost
more), which is why 6>12 by wall. Normalized: ~22s fixed interpreter-bootstrap
of the driver itself + ~0.8ms/char parse. Extrapolating main.spl's closure
(~518 modules, est. multi-100k chars) → ~70–90 min of interpreted parse before
codegen — matches the reported 90-min wall. It is heavy-LINEAR, not superlinear.

### 3. Pruning — ALREADY optimal, not the problem

main.spl's transitive import closure = **518 files out of ~10,657** total
(`src/compiler` 345, `src/app` 65, `src/std` 53, `src/lib` 29, `src/os` 26).
`--entry-closure` already prunes 10,657→518 and the driver's implicit whole-src
bulk-load is correctly suppressed (`driver.spl:301-302`, verified
`[load_sources] total 6` for context). The 518 are genuinely reachable — no
cheap pruning win remains. The cost is interpreted parse × the reachable set.

### 4. parser_error verdict — FRONTEND FEATURE GAP, not a stale binary

Reproduced on the deployed binary. Two distinct current-syntax constructs the
self-hosted frontend `parse_full_frontend` does NOT accept:
- **`mut` parameters** (`pattern_dispatch.spl:193` `fn rewrite_block(..., mut stats: PatternIdiomStats)`): `expected ), got Ident`. The `Param` struct (`src/compiler/10.frontend/parser_types.spl:139`) has NO `is_mut` field and no parser code consumes `mut` in param position → **the current frontend source itself lacks the feature** (74 repo files use `mut` params).
- **irrefutable destructuring `val`** (`variables.spl:358` `val Some(dollar_idx) = dollar_pos`): `expected =, got (` (226 repo files use `val Some(...)=`).

Decisive: `simple run` (interpreter) PARSES both fine but its HIR-lowering
rejects the destructuring let ("complex patterns not yet supported in let
bindings"); `simple check`/native-build's `parse_full_frontend` rejects `mut`
at PARSE time. So the interpreter parser and the self-hosted parser DIVERGE —
compiler sources were written/tested against the richer interpreter parser.
Error RECOVERY is NOT slow (mut file 7.9s ≈ clean file 8.4s), so this is a
correctness blocker, not (much of) the perf wall. But it IS a hard second
blocker: main.spl's 518-closure contains `mut`-param files (e.g.
pattern_dispatch.spl), so even a fast build would emit these errors and produce
broken modules. **A working full-CLI self-host requires teaching
`parse_full_frontend` `mut` params + the HIR let-lowering destructuring.**

### 5. What was spiked / landed

- LANDED (safe, default-off): timestamped `[BOOTSTRAP-PHASE]` profiler +
  per-file parse markers (`driver_log_helpers.spl`, `driver.spl`) — serves
  Next-Step #1 ("profile the phase") and produced every number above.
- NOT landed: no small pure-Simple perf fix exists. The wall is interpreted
  execution of the frontend; there is no redundant work / O(n²) / cache miss to
  remove within a single fresh build (parse-once already holds; closure already
  minimal). A path+content-hash parse cache would only help REPEATED builds, and
  robust AST (de)serialization is a large/risky change — deferred.

### Remaining plan to a working full-CLI build (in priority order)

1. **Perf (root fix): run the frontend COMPILED, not interpreted.** native-build
   currently dispatches through `cli_run_file` → interpreter. Options: (a) fix
   the interpreter JIT fall-back so the parser hot path is JIT/AOT-compiled
   (`run` logs "JIT compilation failed, falling back to interpreter"); (b)
   register native-build/build as compiled builtins that call the linked-in
   `compiler_driver_run_compile` directly. Expected: ~0.8ms/char → ~0.01ms/char
   class (≈50–80×), turning ~90 min into ~1–2 min. This is architectural and
   cannot be proven without a rebuild (blocked by #2), so it is a plan, not a
   spike.
2. **Frontend feature gap (correctness blocker):** add `mut`-param support to
   `parse_full_frontend`/`Param` and destructuring in HIR let-lowering, OR strip
   `mut`/destructuring from the ~74+226 sources in the closure. Without this the
   build fails at parse even once fast. Testable via interpreted `check` on a
   `mut` file.
3. **Iteration relief (optional):** persistent parse cache keyed on
   path+content-hash to skip re-parse across bootstrap re-runs (helps the
   "blocks rapid iteration" complaint; does not help the first fresh build).
4. Raising `--timeout` alone is a non-fix: it lets phase-2 finish but the build
   then fails on the #2 parser gap.

The misleading timeout hint in `native_build_main.spl`
("use the in-process backend for cross-target builds") is DEBUNKED — in-process
shares the same interpreted parse. (File was under concurrent edit; not
patched here to avoid a clobber.)
