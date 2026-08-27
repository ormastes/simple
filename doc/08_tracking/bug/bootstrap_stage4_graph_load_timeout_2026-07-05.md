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

## Linux confirmation 2026-07-17 — compiled in-process Stage 4 still exceeds 40 minutes

A clean x86_64 Linux publication worktree built `bootstrap_main.spl` with a
pure-Simple Stage 3 compiler in 484.6 seconds (715 compiled, 0 failed). The
result then entered the authorized compiled in-process Stage 4 path for
`src/app/cli/main.spl`, with `--entry-closure`, one thread, a warm 53 MiB
native cache, and the `core-c-bootstrap` runtime lane.

The process remained continuously CPU-active and produced no output before
the explicit 2400-second timeout. RSS grew gradually to about 10.5 GiB. After
the timeout flushed the log, it contained repeated statement-arena diagnostics
for even indices 1706 through 1756 against a live arena length of 462, followed
by `[flat-bridge] missing stmt tag`. A concurrent independent Stage 4 run
showed the same one-CPU profile beyond 46 minutes, ruling out a local
cache/output collision.

Evidence:

- worktree: `/tmp/simple-font-publish-20260717`
- log: `build/native_probe/full-cycle3.log` (78 lines after timeout)
- intended output: `build/native_probe/full-cycle3/simple` (not produced)
- result: exit 124 after 2400 seconds

Initial evidence suggested an arena/environment provenance split, and the
2026-07-17 repair restored local count slots, arena-preferred reads, disabled
environment mirrors, in-place arena reuse, and arena-only declaration tags.
Those are valid ownership/performance repairs, but a rebuilt Cycle 5 candidate
still reproduced the exact OOB series. Reset tracing then localized the first
series (204, 207, 210, 213 against 64 statements) to the four fat-arrow arms
in `src/lib/common/ui/widget.spl`. `parse_match_arms_common` stored each raw
expression ID directly in `arm_body`, whose declared and consumed contract is
statement IDs; the bridge therefore passed expression-arena IDs to
`stmt_get_tag`. The root fix wraps the expression with the existing
`stmt_expr_stmt` constructor. `bootstrap_expr_stmt_arena_spec.spl` now checks
that fat-arrow arm bodies contain `STMT_EXPR` nodes.
A fresh Stage-4 admission run remains required before closing the performance
incident.

## Cycle 6 evidence — cross-arena OOB removed

The rebuilt Cycle 6 candidate compiled 4 changed units with 711 cache hits.
Its bounded Stage-4 run emitted none of the prior statement-arena OOB or
`missing stmt tag` diagnostics. It advanced through frontend loading and then
failed normally in phase 2 at
`src/compiler/60.mir_opt/mir_opt/collection_opt_core.spl:470`: the bootstrap
parser rejected the `mut counts` parameter in `count_inst_uses` with
`expected ), got Ident 'counts'`. This is the next admission blocker; the
fat-arrow match-arm arena defect is no longer the stopping point.

## Cycles 7–9 evidence — three parser gaps removed, admission still open

The mandatory three-cycle follow-up preserved the warm native cache and used
only pure-Simple bootstrap compilers. Each bootstrap candidate rebuilt all 715
units with zero compilation failures and linked successfully:

- Cycle 7 taught impl/class method parsing to consume canonical
  `mut name: Type`, preserve the marker when implicit `self` is prepended, and
  write the aligned `PARAM_MUTS` arena. Stage 4 passed `collection_opt_core.spl`
  and next rejected keyword-named parameter uses such as `loop.header`.
- Cycle 8 disambiguated `loop:` control flow from the established keyword-as-
  identifier forms at both primary-expression and statement dispatch. Stage 4
  passed `loop_licm.spl` and next rejected the widely used `me fn name(...)`
  mutable-method spelling in `src/lib/nogc_sync_mut/db/accel.spl`.
- Cycle 9 accepted both `me name(...)` and `me fn name(...)` through the same
  mutable-method path. Its bounded Stage-4 run passed every earlier blocker,
  then stopped in phase 2 at
  `src/std/nogc_sync_mut/env/variables.spl:362` with
  `expected =, got (` for the destructuring binding
  `val Some(dollar_idx) = dollar_pos`.

The direct pure-parser regression now checks aligned method names/mutability,
leading `loop.header`, both fat-arrow statement wrappers, and `me fn` parsing.
The full CLI and its test runner were not produced, so executable spec evidence,
font/pixel/performance evidence, production verification, and publication remain
open. Per the three-cycle cap, the `val Some(...)` parser gap is recorded here
for the next scoped session rather than repaired or retried in this one.

## Cycles 10–11 evidence — `Some(...)` binding repaired, graph timeout remains

The next scoped session added direct pure-parser support for the production
`val Some(name) = expression` and `var Some(name) = expression` forms. The
binding evaluates the initializer once and lowers its payload to
`expression.unwrap()`. Plain `val Some = expression` remains an ordinary name.
Malformed constructor bindings consume their initializer and return a recovery
statement instead of falling through at `=` and cascading diagnostics.

Cycle 11 rebuilt the reviewed final source with the retained cache and the
Cycle 10 pure-Simple bootstrap candidate: all 715 units compiled, zero failed,
and `build/native_probe/simple-cycle11` linked in 401.5 seconds. A higher-model
review reported PASS for the token progress, recovery, AST lowering, and the
positive, mutable, malformed, and fallback parser regressions.

The one bounded Cycle 11 Stage-4 admission run used that exact candidate and
continued at full CPU with no parser/lowering diagnostic, including no
recurrence of the earlier `variables.spl` error. It reached the 900-second
timeout before linking `build/native_probe/full-cycle11/simple`. Therefore the
grammar blocker is repaired, but full-graph admission performance remains open.
No Rust-seed fallback was used, and the missing admitted full CLI still blocks
execution of the focused specs, font/pixel evidence, verification, and push.

## Frontend arena-owner restoration — 2026-07-19

The reviewed `f0a5601842`/`ee4d21b4bf` arena-owner bundle is restored without
reverting later reset, parser, or field-default fixes. Expression and statement
counts/mode flags are cached; native arena mode no longer mirrors every node
through the process environment; declaration and module reads stay within their
arena and use integer environment reads only for mode gates. The deleted native
arena isolation spec is restored, the stale declaration/interpreter mirror
cases are reinstated, and an exact `parser.spl` self-parse regression is added.
Bounded seed diagnostics pass the arena isolation spec 3/3, both reinstated
mirror cases, and the parser self-parse 1/1. The broader declaration-count spec
is 7/9 under the seed: its direct imported-array large/small assertion and
GPU/asm side-arena reset scenario still fail across seed interpreter module
boundaries. The seed's generic `test` wrapper reports no examples and
`check src/compiler` delegates to the absent admitted `bin/simple`, so those
are not product-admission claims or an overall green test claim.

One incremental pure-Simple Stage2/Stage3 rebuild passed both compiler sanity
checks and Stage2 native-build capability. Its hashes are
`33e0c7b6852a01497b1fd29d46af2d4241a1218d64bf1a3013701b7620dbe814`
(Stage2) and
`3599de8c8711b6a3a0582e1d03191e6c5997352161c889c6b3401fcc07f30850`
(Stage3).

The single bounded Stage4 profile proves a large improvement and exposes the
next blocker. `parser.spl` parsed cleanly; the run completed 50 files in about
59 seconds, versus 43 files in 380 seconds before restoration. It then reached
the 8 GiB address-space ceiling while starting
`src/lib/nogc_async_mut/database/bug.spl`: glibc failed to register a TLS
destructor and aborted at 63.51 seconds with 8,370,968 KiB peak RSS. The timeout
directly owned the compiler PID and the full process chain exited, so no orphan
remained. Evidence is retained in
`build/native_probe/stage4-arena-restore.{log,time}`. The parser corruption and
per-node environment wall are fixed; retained allocation growth remains the
next focused blocker. Because this profile used Stage3 while earlier
long-progress profiles used Stage2, one 90-second Stage2 A/B ran under the same
one-thread/8 GiB envelope. It reproduced the same 50-file frontier, clean
`parser.spl`, active `database/bug.spl`, TLS-destructor OOM, and 63.86-second
abort at 8,371,548 KiB peak RSS. Compiler generation is therefore ruled out.
The next focused owner is phase-two parse scratch/runtime allocation lifetime;
do not patch TLS, raise the cap, or rerun Stage4 before a narrow allocation
count/RSS regression exists.

## Hosted heap-registry diagnostic — 2026-07-19

A single hosted-only `rt_heap_registry_count()` diagnostic now reports the
number of registered runtime heap objects. Rust reads its heap registry length;
Core-C maintains a relaxed atomic total across its five append-only registries.
The existing phase-profile logger appends the count to every enabled marker, so
the next bounded Stage4 run can correlate per-file parse progress with object
growth without adding an unconditional hot-path probe. The symbol is explicitly
classified hosted-only and is not part of the pure-Simple core-required ABI.

The runtime ABI classification test passes 1/1, and the process-isolated
Core-C runtime focus probe compiles and passes under a 2 GiB/60-second cap. A
parallel Rust global-delta unit was rejected because the shared registry makes
it suite-order dependent; the process-isolated C probe and sequential Simple
arena spec carry the behavior checks instead. The incremental seed rebuild did
not complete: rustc exhausted its output filesystem while producing the large
single-codegen-unit compiler artifact. No Stage4 retry or full bootstrap was
started. Rebuild the seed/native-all artifacts separately when storage permits,
then run the updated arena spec once before the next bounded profile.

## Per-file flat pool isolation — 2026-07-19

The isolated rich-module path reset AST/statement/expression arenas but left
the flat span, token, symbol, named-type, signature, and composite-type pools
live across files. `parse_and_build_module` now resets those pools at its
isolated-file boundary. The shared multi-file append compiler remains unchanged.
`reset_all_pools` also retains each outer array and clears it in place instead
of registering 37 replacement arrays on every reset.

A 2 GiB/60-second direct pure-Simple probe parsed two entry-shaped modules,
preserved the first returned rich module, rejected its stale named-type entry,
assigned the second module's first named type ID at zero, and printed
`type_pool_reset_ok`. The generic spec runner still traversed the unrelated
600+ file library before the scenario body, so it is not counted as evidence.
No Stage4 retry was started because another active session already owns that
run; RSS impact remains unproven.

## Per-token lexer scratch reuse — 2026-07-19

The externally owned Stage4 v45 profile used the current compiled Stage4 route
and terminated at its 1,200-second cap without a candidate. Import discovery
finished at +38.293 seconds; 40 files completed by +346.179 seconds;
`src/compiler/10.frontend/core/lexer_struct.spl` started at +346.203 seconds
and never emitted its done marker. The compiler remained CPU-active for the
full envelope and reached about 6.9 GiB RSS, so the file had roughly 854
seconds rather than being an incidental last-file cutoff. Retained evidence is
`/tmp/simple-tooling-hardening-land/build/bootstrap/tooling-stage4-v45/build.log`;
the outer redirected log remained empty.

`CoreLexer.char_slice` already joined token spans once, but still registered a
new temporary `[text]` array for every token. It now keeps one per-lexer
`slice_parts` array and clears/reuses it for each span. The lexer facade and
token behavior are unchanged. The existing five-case lexer regression passes
once under the explicitly bounded Rust bootstrap repair runner; this is not a
product admission claim. `simple optimize` and generated-manual refresh remain
unavailable until a pure-Simple CLI is admitted.

Do not repeat Stage4 in this session. The next fresh cycle may refresh the
cached Stage2/Stage3 pair with this source, run the same lexer regression under
the admitted CLI, then perform one bounded Stage4 A/B against the v45
40-file/6.9-GiB baseline.

## Re-verification 2026-08-17 (fleet lane C)

STILL-OPEN, unproven either way. `src/compiler/99.loader/module_loader.spl` exists (603 lines)
but contains no `timeout`/`7200` handling, and the `module_graph.spl` the doc cites is absent
from disk (path drift confirmed). Reproduction requires a full stage-4 native build under
`scripts/bootstrap/bootstrap-from-scratch.sh` — explicitly out of bounds for this lane while
the users stage-3 bootstrap owns the host. No patch attempted.
