# Stage-4 ignores `--threads` entirely — two independent layers both discard
# it (pure-Simple frontend driver has no fanout concept; AOT codegen's
# "ParallelBuilder" computes a worker count and then runs sequentially anyway)

**Date:** 2026-07-18 · **Lane:** S79 (root-plumbing trace) + S80 (fix +
follow-up) · **Status:** PARTIALLY FIXED — S79 traced both layers end to end
with code citations, confirmed empirically (A/B thread-count probe below); no
source fix landed in S79 (see "Why no fix" below). **S80 update:** fixed the
`bootstrap_main.spl` Stage4 `--threads`-discard gap (item independent of the
codegen `ParallelBuilder`); investigated wiring `build_parallel()` and
determined it is not safely landable without new MIR-serialization
infrastructure that does not yet exist (see "S80 update" section below for
the empirical case) — that part remains OPEN, deferred with evidence rather
than fixed.

## Summary

Stage 4's full-CLI native-build (`--entry src/app/cli/main.spl --mode
one-binary` under `SIMPLE_BOOTSTRAP_STAGE4=1`, per
`scripts/bootstrap/bootstrap-from-scratch.sh:464-491`
`bootstrap_native_build_main()`) passes `--threads "${selfhost_jobs}"` (8 on a
32-core box) all the way through the CLI arg parser, but the process runs
with exactly **one OS thread (`nlwp=1`) for its entire life**, regardless of
the requested thread count. This was independently observed by two prior
lanes (S66, S77 — see `doc/08_tracking/bug/stage4_full_cli_closure_spin_2026-07-18.md`
Follow-up #3, which named this investigation) and is now confirmed with a
direct empirical A/B probe (below) plus an exact code trace explaining
**why**: the requested `--threads` value is silently discarded before it ever
reaches a thread pool, because Stage 4 does not execute the code path that
owns the thread pool at all.

## Named root cause

**Stage 4 deliberately does not call the parallel Rust `native-build`
pipeline.** `src/app/cli/bootstrap_main.spl:171-204`
(`run_native_build_bootstrap`):

```
val explicit_entry = native_build_entry_from_args(args, 0)
if explicit_entry != "":
    if env_get("SIMPLE_BOOTSTRAP_STAGE4") != "1":
        return run_rt_native_build(args)          # <- Rust FFI, rayon pool, honors --threads
    ...
    val stage4_result = aot_native_project_with_backend_fixed(
        "", "", "", "", "", 0,
        explicit_entry, stage4_output, stage4_backend, true, true, 3
    )                                              # <- pure-Simple in-process driver, NO thread param
```

When `SIMPLE_BOOTSTRAP_STAGE4=1` is set (always true for real Stage 4 runs)
and an explicit `--entry` is given (always true — Stage 4 always passes
`--entry src/app/cli/main.spl`), the branch taken is
`aot_native_project_with_backend_fixed`, **not** `run_rt_native_build`. The
comment at lines 166-170 explains this is intentional (#138/#19): Stage 4
exists to dogfood the pure-Simple in-process compiler pipeline as a
bootstrap-verification step, not to shell out to the Rust seed's native-build
implementation. **This is why the obvious "cheap fix" — just route Stage 4
through `run_rt_native_build` — is wrong**: it would silently swap Stage 4
back to compiling with the Rust seed, defeating the entire point of the
stage (verifying the self-hosted compiler can build itself).

`aot_native_project_with_backend_fixed`
(`src/compiler/80.driver/bootstrap_api.spl:47-105`) has **no thread-count
parameter in its signature at all** — it builds `CompileOptions`, calls
`compiler_driver_create(options)`, then `compiler_driver_run_compile(driver)`
(`src/compiler/80.driver/driver.spl`). The Rust rayon thread pool
(`init_rayon_pool`, `src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:78-106`,
gated by `self.config.parallel` at line 519 and `compile_entries_parallel` vs.
`compile_entries_sequential` at lines 728-732) lives entirely inside
`NativeProjectBuilder::build()`, which only `run_rt_native_build` can reach.
`--threads` is captured by `native_build_flag_needs_value` in
`bootstrap_main.spl:52-53` purely so the bootstrap-side arg scanner knows to
skip its value token — the value itself is never read or forwarded into
`aot_native_project_with_backend_fixed`'s call.

**Conclusion on the task brief's three hypotheses:** (a) is correct and
precise — the Stage4 env flag routes to a code path
(`aot_native_project_with_backend_fixed` → pure-Simple `CompilerDriver`) that
has no thread-count concept whatsoever, not merely one that "ignores" a
value it received. (b) is also correct as a consequence: the pure-Simple
frontend's per-file parse loop is inherently serial by design — see below,
it is not merely "not yet parallelized," it actively depends on global
mutable state that forbids naive parallelization. (c) is refuted: threads
were never meant to apply to the Rust `native_project` phase alone — that
phase is fully bypassed for Stage 4; the *only* phase that ever runs for
Stage 4 is the un-parallelized pure-Simple one.

## Why per-file parse cannot be naively fanned out (checked per task item 3)

The phase2 per-file loop actually executed
(`src/compiler/80.driver/driver.spl:628-652`,
`for source in unique_entry_sources: ... parse_full_frontend(...)`) calls
into a chain with **extensive shared, non-thread-local global state**:

- `parse_full_frontend` (`src/compiler/10.frontend/frontend.spl:64`) →
  `parse_and_build_module` (`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:614-629`)
  calls `parser_init_with_path(source, path)` at the top of **every** file's
  parse.
- `parser_init_with_path` (`src/compiler/10.frontend/core/parser.spl:214-233`)
  reassigns a long list of **module-level global variables** on every call:
  `par_errors`, `par_warnings`, `par_struct_names`, `par_kind_slot`,
  `par_text_slot`, `par_line_slot`, `par_col_slot`, `par_src_cache_slot`,
  `par_src_cache_gen_slot`, `par_had_error`, `par_diagnostics_suppressed`,
  `par_diagnostic_emit_count` — plus calls `ast_reset()` (a global AST arena
  reset), `module_set_path(path)` (global "current file" state), and
  `lex_init_with_path(source, path)` (global lexer state).
- `parse_and_build_module` (module_assembly.spl:615-616, 626-628) additionally
  saves/restores lexer state through **process environment variables**
  (`SIMPLE_BOOTSTRAP_LEX_SOURCE`, `SIMPLE_BOOTSTRAP_LEX_PATH`) and bumps a
  global `parser_lex_source_gen_bump()` generation counter. Environment
  variables are process-wide, not thread-local; concurrent `env_get`/`env_set`
  from multiple OS threads racing on the same keys is undefined behavior in
  general and specifically corrupts exactly the save/restore invariant this
  code depends on.

Any naive per-file thread fan-out over this loop — e.g. via the stdlib's
`spawn_isolated`/`parallel_map` (`src/compiler_rust/lib/std/src/concurrency/threads.spl:156,414`)
— would have every worker thread stomping the same `par_*`/AST-arena/lexer
globals and the same env-var keys concurrently. `spawn_isolated`'s "isolation"
deep-copies only the **data argument** passed into the closure; it does
**not** give each OS thread its own copy of file-scope `var` globals compiled
into the binary's shared address space. Using it here would silently
interleave/corrupt parses across files — exactly the "convert a loud failure
into a silent wrong answer" class of bug this campaign is explicitly
forbidden from introducing. **This is a hard blocker, not a missing
convenience wrapper**: making phase2 parallel-safe requires converting all of
the above into either thread-local storage or an explicit per-call
`ParserSession`/`LexerSession` struct threaded through the whole
lex→parse→AST-build chain — a real, invasive refactor spanning
`core/parser.spl`, the lexer, and the flat-AST arena, not a scoped
single-lane change.

Phase 3 (HIR lowering) is **not** a safer fallback target either:
- `driver.spl:817` shows the "unstub_reparse" branch calls
  `parse_full_frontend` **again**, per file, hitting the identical global-state
  hazard — and this redundant re-parse is the separately-tracked
  `doc/08_tracking/bug/stage4_entry_closure_duplicate_parse_2026-07-17.md`
  (compounding factor, explicitly out of scope to fix here).
- `driver.spl:857` (`shared_lowered_traits = lowering.lowered_traits`) is an
  **intentional, ordered, cross-file data dependency**: each module's newly
  lowered traits fold forward into a registry consumed by later modules'
  trait-default-method resolution. Phase 3 is not embarrassingly parallel by
  design even setting aside the global-state problem — parallelizing it
  would need a two-pass scheme (collect all trait impls serially first, then
  lower bodies in parallel), not a plain fan-out.
- AOT codegen (`aot_compile()` and beyond, phase5+) **was traced** (see next
  section) — a second, independent, more narrowly-scoped bug was found there.

## Second finding: AOT codegen has its own fake-parallel builder (checked per
## task item 3's "or the later codegen jobs" fallback)

`aot_compile()` (`driver.spl:1049`) reaches `compile_to_native()`
(`src/compiler/80.driver/driver_aot_output.spl:260`) for Stage 4's default
native-executable output. That function's per-module object-compile step
(lines 355-378) **does** organize codegen as independent, cacheable,
per-module units — each module gets its own object file
(`{object_base}.{name}.o`, line 390) via `_compile_one_module` — and
explicitly builds a `ParallelBuildConfig` with `num_threads:
driver_native_build_threads()` (line 367), which reads
`SIMPLE_NATIVE_BUILD_THREADS` (`driver_aot_output.spl:68-75`) — an env var
the real bootstrap script **does** set
(`SIMPLE_NATIVE_BUILD_THREADS="${selfhost_jobs}"`,
`bootstrap-from-scratch.sh:472`). So far this looks like real, correctly-wired
parallelism for codegen, unlike phase2/phase3.

**It is not.** `src/compiler/80.driver/driver_build/parallel.spl` contains
**two** build methods:

- `build_parallel(spawn_fn, collect_fn)` (line 394) — genuinely parallel: it
  calls `spawn_fn(build_unit.path)` which is meant to call
  `rt_process_spawn_async` (declared at line 9) to launch each module's
  compile as a **separate OS process**. The file's own header comment (lines
  5-6) explains why: *"Uses process-based parallelism ... to avoid
  thread-safety issues with global compiler state"* — independent
  confirmation, from the codebase's own prior author, of the exact same
  global-mutable-compiler-state hazard this lane found in the parser.
- `build(compile_fn)` (line 281) — **this is the one actually called**
  (`driver_aot_output.spl:377`, `builder.build(_compile_one_module(...))`).
  Its "parallel" branch (lines 336-389, taken whenever `uncached_names.len()
  >= parallel_threshold`) computes `max_workers =
  self.config.effective_threads()`, prints `"[PARALLEL] batch-concurrent
  mode, {max_workers} workers"` (line 340), and organizes units into chunks
  of size `max_workers` (lines 353-389) — **but the chunk-execution loop
  (lines 366-387) calls `compile_fn(build_unit.path)` synchronously, one unit
  at a time, in-process, with no thread or process spawned anywhere in this
  method.** The chunk boundary has zero effect on execution — it is
  computed and then ignored. `build_parallel` (the real implementation,
  right below it in the same file) is never invoked by any AOT codegen call
  site: it is dead code from `compile_to_native`'s perspective.

**Net effect:** even in the (currently unreached, per the A/B probe below)
event that a Stage 4 run gets far enough to start compiling object files, it
would still compile them **one at a time**, despite `--threads 8` /
`SIMPLE_NATIVE_BUILD_THREADS=8` being correctly parsed, correctly forwarded,
and used to print a worker count that is never acted on. This is a second,
independently-diagnosable instance of the same class of bug as the top-level
finding (`--threads` computed and displayed but not applied) — but far more
narrowly scoped: the fix is "call `build_parallel` instead of `build`" plus
adapting `_compile_one_module`'s contract to a spawnable subprocess shape.
That adaptation is **not trivial**: `_compile_one_module` (line 796) takes
the full shared in-process `ctx: any` (all already-lowered MIR modules held
in one `CompileContext`) and calls straight into the codegen backend
in-process; making it subprocess-spawnable would mean either re-deriving each
module's MIR inside a freshly-invoked subprocess (expensive, needs its own
serialization contract) or serializing/passing the relevant MIR module across
the process boundary. Concretely scoped, but genuinely a build-out task, not
a one-line change — **not attempted in this bounded lane** (no full
bootstrap available to verify a codegen-path change end-to-end; a wrong
subprocess-argument or object-collection contract here would silently
produce a corrupt or incomplete binary, exactly the failure mode this
campaign must avoid).

Whether this codegen-level bug or the phase2/phase3 frontend bug dominates
Stage 4's actual multi-hour wall time was not measured in this lane (the A/B
probe below shows Stage 4 still deep in phase2:parse after 91-116s elapsed
and prior lanes report 11-20+ min still short of finishing that phase on the
real command) — both are real, both are cited with exact fix locations, and
both are left for the next lane to prioritize with fresh wall-clock data.

## Empirical A/B confirmation (this lane, current worktree)

Using the read-only prebuilt Stage-3 binary from
`/home/ormastes/dev/wt_s58/build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple`
(sha256 `daf91ae650...`, copied into this worktree's own `build/s79_probe/`
scratch, never written into wt_s58), same machine, both runs `--threads 8`:

**Probe A — WITHOUT `SIMPLE_BOOTSTRAP_STAGE4`** (tiny synthetic entry
importing `compiler.driver.driver`, `--entry-closure`, so `explicit_entry !=
""` but the STAGE4 env check at bootstrap_main.spl:178 is false → routes to
`run_rt_native_build` → Rust `NativeProjectBuilder::build()`):

```
$ ps -o pid,nlwp,rss,etimes -p $PID   # sampled every 5s
  95325    9   19808    6
  95325    9   39588   11
  95325    9   84176   16
  95325    9  143160   21
  95325   17  215268   26
  95325   17  295092   31
  95325   17  361204   36
  95325   17  317276   41
```
Log: `Found 662 .spl files`, `Import map: 16689 unique, 1029 ambiguous...`,
`Incremental: 0 cached, 662 to compile`, progress reaching `[650/662]
compiled` by t≈41s. **nlwp jumps to 9 immediately (8 rayon workers + main)
and later to 17** — real, working parallelism, `--threads 8` honored.

**Probe B — WITH `SIMPLE_BOOTSTRAP_STAGE4=1`** (real Stage-4 shape:
`--source src/compiler --source src/app --source src/lib --source
examples/10_tooling --entry-closure --low-memory --threads 8 --mode
one-binary --entry src/app/cli/main.spl`, matching
`bootstrap-from-scratch.sh:478-490` exactly):

```
$ ps -o pid,nlwp,rss,etimes -p $PID   # sampled every 5s
  85543    1   4263544   91
  85543    1   4295488   96
  85543    1   4332768  101
  85543    1   4352936  106
  85543    1   4383840  111
  85543    1   4425360  116
```
**`nlwp` stays pinned at 1 for the entire sampled window** (91s-116s
elapsed; process had already been running before sampling started) while
RSS climbs steadily (4.16 GB → 4.32 GB, no plateau) — the process was
confirmed still inside `phase2:parse` (21 `phase2:parse:file:start` markers
seen, up to `src/app/cli/browser.spl`) via `SIMPLE_COMPILER_TRACE=1` (note:
this trace flag adds significant per-token overhead beyond production
`--low-memory` runs, so absolute file-count-per-second here understates real
Stage-4 throughput, but the `nlwp=1` observation is unaffected by tracing
overhead). This matches S66/S77's independent field observations exactly.

Both processes were killed after data collection (no full compile run;
`build/s79_probe/` scratch removed afterward, `wt_s58` untouched — verified
via checksum before and no writes after).

## Why no source fix in this lane

Two independent fixes are named, both real work, neither safely landable
blind in a bounded no-full-bootstrap lane:

1. **Frontend (phase2/phase3):** requires converting a wide swath of
   `core/parser.spl` + lexer + AST-arena module-level globals into
   thread-local or explicit per-call session state — a genuine cross-cutting
   refactor, not a "safe, scoped" addition a single lane should land
   speculatively.
2. **Codegen (`ParallelBuilder.build`):** requires either adapting
   `_compile_one_module` to a subprocess-spawnable contract (matching the
   already-written but unused `build_parallel`), or replacing `.build`'s
   in-process chunk loop with a real in-process thread fan-out — the latter
   only safe once (1) is confirmed not to also apply to the codegen backend's
   own global state (not verified in this lane).

Per the standing incremental/scoped-only order and the hard rule against
reordering diagnostics into nondeterministic/silently-wrong output, and given
this lane has no full-bootstrap verification available, both are filed as
precisely named, cited, empirically-confirmed gaps instead of guessed
patches.

## Follow-ups for the next lane

1. Refactor `core/parser.spl`'s `par_*` globals, the lexer's globals, and the
   flat-AST arena (`ast_reset()`) into an explicit `ParserSession` struct (or
   thread-local storage) so `parse_full_frontend` becomes safely re-entrant
   across OS threads. This is the prerequisite for anything below.
2. Once (1) lands, fan out `driver.spl:628-652`'s per-file loop using the
   stdlib's `spawn_isolated`/`parallel_map`
   (`src/compiler_rust/lib/std/src/concurrency/threads.spl:156,414`) — these
   primitives exist and are used elsewhere in the repo; note `spawn_isolated`
   only deep-copies the data argument, so it does not by itself solve (1).
3. Also stop the `SIMPLE_BOOTSTRAP_LEX_SOURCE`/`SIMPLE_BOOTSTRAP_LEX_PATH`
   env-var round-trip in `module_assembly.spl:615-616,626-628` — process env
   vars cannot be made per-thread-safe; this needs to become an explicit
   passed value regardless of the threading refactor.
4. Phase 3's `shared_lowered_traits` (driver.spl:857) needs a two-pass design
   (serial trait-collection pass, then parallel lowering pass) before it can
   be fanned out — do not naively parallelize the existing single-pass loop.
5. **Likely cheaper/higher-value than (1)-(4):** wire
   `compile_to_native`'s call site (`driver_aot_output.spl:377`) to
   `ParallelBuilder.build_parallel(spawn_fn, collect_fn)`
   (`driver_build/parallel.spl:394`, process-based, already thread-safety-aware
   by construction) instead of the current `.build(compile_fn)`
   (`parallel.spl:281`), which computes and logs a worker count but executes
   every unit sequentially in-process (lines 336-389). Requires designing a
   subprocess contract for `_compile_one_module`
   (`driver_aot_output.spl:796`) — it currently needs the full in-process
   `ctx` (all MIR modules) and cannot be spawned as-is. First measure how much
   of Stage 4's total wall time is actually spent in codegen vs. phase2/3
   parse/HIR on a real run to know which of (1) or (5) pays off first.
6. The `stage4_entry_closure_duplicate_parse_2026-07-17.md` bug compounds
   the phase2/phase3 finding (every file may be parsed twice); fixing it
   independently reduces total serial work even before any parallelism fix
   lands.

## S80 update (2026-07-18): threads env-var gap fixed; build_parallel wiring
## confirmed infeasible without new MIR-IPC infra — deferred with evidence

**Status change:** the `--threads` silent-discard in the Stage4 bootstrap path
(follow-up item, distinct from the codegen-parallel-builder finding above) is
now FIXED. The `build()`-vs-`build_parallel()` codegen finding remains OPEN,
now with direct empirical confirmation (below) instead of only a code trace,
plus a concrete reason the "obvious" fix (wire `build_parallel`) cannot be
landed safely in a bounded, no-full-bootstrap lane.

### Fix #1 landed: `--threads` was silently dropped in bootstrap_main.spl,
### independent of the codegen-builder bug above

`src/app/cli/bootstrap_main.spl`'s `run_native_build_bootstrap` (Stage4
branch, lines ~171-237) called `aot_native_project_with_backend_fixed(...)`
without ever reading `--threads` out of `args` or setting
`SIMPLE_NATIVE_BUILD_THREADS`. `driver_native_build_threads()`
(`driver_aot_output.spl:68-75`) already reads that env var directly (no
`CompileOptions` field involved) — the missing piece was purely in
`bootstrap_main.spl` never setting it, unlike the sibling CLI path in
`src/app/io/_CliCompile/compile_targets.spl:667-685,822-845` which parses
`--threads`/`--jobs`/`-j` and does the exact save/set/restore this lane
added. **Note:** the real `bootstrap-from-scratch.sh` wrapper (line 472)
already exports `SIMPLE_NATIVE_BUILD_THREADS="${selfhost_jobs}"` itself before
invoking the compiler, so this gap was masked for that one caller; it was
live for any direct `simple native-build --entry ... --threads N` invocation
that doesn't pre-set the env var (e.g. this lane's own probes).

Added `native_build_threads_from_args` (mirrors the existing
`native_build_backend_from_args` recursion pattern) and wired
save/set/restore of `SIMPLE_NATIVE_BUILD_THREADS` around the
`aot_native_project_with_backend_fixed` call, plus a
`SIMPLE_COMPILER_TRACE`-gated `[S80-THREADS]` print for diagnosis.

**Verification (testability question resolved):** the prebuilt Stage-3
binary at `wt_s58/build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple`
(sha256 `daf91ae650...`, same one S79 used) does **not** interpret
current-source `.spl` — it is a natively-compiled, frozen artifact. Proof:
running it with `SIMPLE_BOOTSTRAP_STAGE4=1 SIMPLE_COMPILER_TRACE=1` against
the real Stage4 CLI shape reached `phase1:load_sources`/`phase2:parse`
(confirmed via existing trace markers) but never printed the new
`[S80-THREADS]` marker, which sits *before* those phases in the edited
source. Getting a natively-recompiled test binary that reflects this edit
requires recompiling the whole `bootstrap_main.spl` closure (it transitively
imports the entire compiler driver/backend to call
`compiler_driver_create`/`run_compile`), which is the same-order cost as a
real Stage4 build (parse alone runs 20+ minutes per S66/S77/S79) — not
achievable as "incremental" in this lane. Fell back to the Rust **seed**
binary (`wt_s58/src/compiler_rust/target/bootstrap/simple`, sha256
`bbddb617e6...`, copied read-only into this worktree's own scratch) running
`bootstrap_main.spl` as an interpreted script
(`simple_seed src/app/cli/bootstrap_main.spl native-build --entry
src/app/cli/main.spl --mode one-binary --threads 8 ...` with
`SIMPLE_BOOTSTRAP_STAGE4=1 SIMPLE_COMPILER_TRACE=1`): this **does** read
current source, and printed `[S80-THREADS] requested_threads=8 old_env=nil`,
confirming the parse/env-set logic is correct. (Interpreting the full
compiler this way is far too slow to run to completion — killed after the
marker was captured.)

**Honest caveat on impact:** on the 32-core box these probes ran on,
`ParallelBuildConfig.effective_threads()` auto-detects and caps at 8
regardless of whether `SIMPLE_NATIVE_BUILD_THREADS` is set (same value
`selfhost_jobs` already resolves to in practice) — so this fix changes
*correctness* (the value is no longer silently discarded) but is not
expected to change observable `nlwp`/wall-time on this hardware. It matters
on machines/values where the explicit request differs from the auto-detected
cap, and for direct CLI use outside the wrapper script.

### Fix #2 (`build()` vs `build_parallel()`): investigated, NOT wired —
### here is the empirical case for why not

Read both implementations in full
(`src/compiler/80.driver/driver_build/parallel.spl`) plus `git log -p` for
the file: it was authored whole in one commit
(`7c30ce49d04`, "wip: working-copy snapshot", 2026-07-04) with **both**
`build()` and `build_parallel()` already present — `build_parallel()` was
never wired to any call site at any point in history and never reverted; it
is not a parked/known-broken feature, just an unfinished one. The only two
subsequent touches to the file (`050209d9b3`, `2043f801145`) are unrelated
bugfixes (ready-queue dedup, tuple-field-name removal), not builder-wiring
changes.

`build_parallel(spawn_fn, collect_fn)` calls `spawn_fn(build_unit.path)` to
launch **a separate OS process** per module via `rt_process_spawn_async`
(declared line 9), polls with `rt_process_is_running`/`rt_process_wait`
(bounded backoff polling in `wait_for_finished_process`, 10ms→25ms→100ms),
and on completion calls `collect_fn(exit_code, path)` to read the result.
Failure modes it already handles: spawn failure (`pid < 0` →
`mark_failed`), a dependency failing upstream (skips descendants), and early
exit (drains + `rt_process_kill`s any still in-flight processes). It is a
complete, self-consistent process-pool implementation — the missing piece is
entirely on the **caller** side: nothing has ever defined what `spawn_fn`
should exec or what `collect_fn` should read, because doing so requires a
module to be independently compilable in a fresh process.

**Why that's not a safe scoped fix here, checked concretely (not just
theorized):**

1. **No MIR IPC exists.** `_compile_one_module`
   (`driver_aot_output.spl:796`) takes the full in-process `ctx: any` (every
   already-lowered `MirModule` for the whole compile) and calls
   `compile_module_with_backend` in the same process. A subprocess doing
   real per-module codegen needs that one module's `MirModule` handed across
   the process boundary. Checked for existing infra:
   `src/compiler/50.mir/mir_serialization.spl` re-exports
   `serialize_mir_module` from `mir_json.spl`, but (a) it is dead code —
   `grep -rl serialize_mir_module src/compiler` finds only its own
   definition and the `__init__.spl` re-export, no caller anywhere — and (b)
   its own comment says "functions-only compatibility shape", i.e.
   incomplete even as a write path. **There is no deserializer at all** (no
   `parse_mir_module`/`from_json` function exists anywhere in
   `src/compiler/50.mir/`). Building one that faithfully round-trips MIR's
   instruction/type/operand/terminator system is a genuine, sizable,
   error-prone task — not a wiring change — and an imperfect deserializer
   would risk silently mis-codegenning an edge-case instruction into a
   corrupt binary, exactly the failure class this campaign forbids.
2. **The alternative (re-invoke the whole pipeline per subprocess instead of
   serializing MIR) is a likely net perf loss, not just extra engineering.**
   `compile_to_native`'s `BuildCache` only caches **post-codegen object
   files**, keyed under a `cache_scope_root` suffixed by
   `driver_native_sources_fingerprint(ctx.sources)` — an aggregate hash over
   *all* loaded sources (`driver_aot_output.spl:113-124`, "any loaded source
   change gets a new object-cache scope"). Phase2/phase3 (parse + HIR/MIR
   lowering) have no persistent cache at all per the finding above. So a
   subprocess that re-ran the driver from scratch to reach codegen for one
   module would re-parse and re-lower the **entire entry closure** every
   time — for Stage4 specifically, that's the 20+ minute phase already
   established as the dominant serial cost. Spawning N such subprocesses
   concurrently does not avoid this; it duplicates that cost N times across
   cores that could otherwise be idle or doing useful work, on top of the
   parse work the *parent* process already did once to reach codegen. This
   would very plausibly make Stage4 slower, not faster.
3. **The backend has the same global-mutable-state hazard the parser has**,
   independently confirmed (not assumed): `grep -n "^var "` across
   `src/compiler/70.backend/` finds module-level globals including
   `_llvm_bootstrap_ir_text`/`_llvm_simpleos_header`
   (`backend/llvm_ir_builder.spl:15-16`),
   `_llvm_bootstrap_string_global_text`
   (`backend/_MirToLlvm/asm_constraints_helpers.spl:20`), and a
   `llvm_bootstrap_last_object_path()` side-channel that
   `_compile_selected_module` reads when `SIMPLE_BOOTSTRAP=1`
   (`driver_aot_output.spl:841-844`) — and `SIMPLE_BOOTSTRAP=1` **is** set
   for the real Stage4 build (`bootstrap-from-scratch.sh:468`,
   `bootstrap_native_build_main`). This confirms the file's own header
   comment (process-based parallelism "to avoid thread-safety issues with
   global compiler state") is correct and that a real in-process
   thread-based fan-out (sidestepping the MIR-IPC problem by staying in one
   process) is **not** a safer shortcut either — it would hit this exact
   hazard. Process-based IPC is the only safe design; it just isn't wired
   yet, and wiring it needs (1) solved first.
4. **Cannot be empirically verified in this lane even if built.** Per the
   probe below, a small/fast test *does* enter `build()`'s parallel-chunk
   branch, but the real Stage4 shape does not reach codegen at all inside a
   bounded probe window (parse-bound, matching every prior lane's
   observation) — so a build_parallel change could not be validated
   end-to-end against the actual target scenario without a full bootstrap,
   which is out of scope for this lane. An unverified subprocess/IPC change
   to the codegen path is exactly the kind of "loud failure converted to
   silent wrong answer" risk this campaign must not take.
5. **The smoke-matrix gate would not exercise this branch either.**
   `build()`'s parallel-chunk branch only activates when
   `uncached_names.len() >= parallel_threshold` (4) with a cold cache
   (`driver_aot_output.spl:365`, `parallel.spl:293`); small smoke-test
   programs typically compile through the `len() == 1` direct
   `_compile_one_module` path instead (confirmed: the matrix run for this
   lane, below, shows no `[PARALLEL]`-branch signature). So a
   build_parallel change would not even be regression-covered by the
   standard gate — another reason not to land it speculatively.

### New empirical confirmation of the `build()` bug itself (this lane)

Rather than leave this as a pure code-reading claim, reproduced it directly
and cheaply — **without** touching `parallel.spl`/`driver_aot_output.spl` (so
this reflects the exact same, unmodified behavior as before this lane) —
using the **deployed self-hosted binary**
(`/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple`,
sha256 `561767c6615b...`, read-only copied into this worktree's scratch,
never modified) against a small synthetic 7-file closure (1 entry + 6
independent modules, no cross-deps, in
`build/s80_probe/parallel_probe/` — gitignored scratch, not committed):

```
$ simple native-build --source parallel_probe --entry parallel_probe/entry.spl \
    --entry-closure --mode one-binary --threads 4 --verbose --cache-dir ... -o ...
```

With `SIMPLE_COMPILER_TRACE=1`, the log shows `[NATIVE] compiling 7
modules...`, compiling in this exact order: `entry, mod_2, mod_3, mod_4` |
`mod_1, mod_6, mod_5` — i.e. two groups of **4 then 3**, precisely matching
`build()`'s parallel-branch chunking (`chunk_end = batch_idx + max_workers`,
`max_workers=4` from `--threads 4`) rather than `topological_order()`'s
would-be insertion/dependency order. This is strong circumstantial
confirmation the parallel-chunk branch (not the deterministic/sequential
branch) was entered. Without trace (same command, `ps -o pid,nlwp,etimes,rss`
sampled every 1s for the full ~36s run): **`nlwp` stayed at exactly `1` for
every sample from t=0s to t=35s** — no additional OS thread or process ever
appeared, confirming the chunk boundary has zero effect on execution, exactly
as the original code-reading finding said. (The synthetic test binary itself
segfaults at runtime — an artifact of the minimal/incomplete test program,
unrelated to the compiler; only the *compile-time* behavior was under test.)

## Related

- `doc/08_tracking/bug/stage4_full_cli_closure_spin_2026-07-18.md` (S77 —
  named `compile_entries_sequential` and asked the exact question this lane
  answers, Follow-up #3)
- `doc/08_tracking/bug/stage4_entry_closure_duplicate_parse_2026-07-17.md`
- `doc/08_tracking/bug/macos_stage4_full_cli_low_memory_runaway_2026-07-17.md`
- `doc/08_tracking/bug/native_build_stage4_pre_object_spin_2026-07-13.md`
