# Coverage tooling does not reproduce end-to-end — no `spl-coverage` CLI in the deployed binary, no branch probes emitted by production MIR lowering, and no coverage artifact written by the spipe/.spl test-runner path

- **Date:** 2026-08-07
- **Severity:** high (planning-blocking) — two landed 2026-08-07 coverage plans
  (`doc/03_plan/ui/testing/render_2d_vulkan_functional_coverage_plan_2026-08-07.md`,
  `doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md`)
  built branch-coverage and line-coverage closure units on top of tooling that
  does not currently work end-to-end. No product functionality is broken by
  this; it blocks trustworthy coverage MEASUREMENT, both branch and line.
- **Status:** open. Structural root causes pinned by source read (file:line
  below); no fix attempted here (doc-only investigation). Five concrete
  prerequisites are listed at the end as the unblock condition.

## Scope: this is BOTH a branch-coverage gap AND a line-coverage-export gap

A prior bug doc
(`doc/08_tracking/bug/instrumented_statement_coverage_tooling_inert_2026-08-02.md`)
already established that branch/decision coverage is inert under `bin/simple
test`. This doc adds two things that doc did not cover: (1) the `bin/simple
spl-coverage` CLI claimed usable by the render_2d plan does not exist in the
deployed binary at all, and (2) **even line coverage — which the wm_gui_web
plan's §1.2 describes as "REAL"** — does not produce a coverage artifact via
the actual spipe/.spl runner path when empirically re-tested on 2026-08-07.
Both landed plans need correcting on this point.

## Empirical repro 1: `spl-coverage` subcommand does not exist

```
$ bin/simple spl-coverage dump
error: file not found: spl-coverage
```

`bin/simple` resolves to `bin/release/x86_64-unknown-linux-gnu/simple`, a Rust
bootstrap seed (per repo policy, the only binary `test`/`build`/`run` should
run against). `src/app/spl_coverage/main.spl` **does exist as SOURCE**
(`ls -la src/app/spl_coverage/` → one file, `main.spl`, 5176 bytes, last
touched 2026-07-30) — so the render_2d plan's claim "Coverage tooling exists:
`src/app/spl_coverage/main.spl` ... `bin/simple spl-coverage dump/status/clear`
does branch/decision coverage" conflates "source file exists in the tree" with
"subcommand is wired into the deployed binary's dispatch table." The dispatch
wiring does not exist — the deployed binary has never heard of `spl-coverage`
as a subcommand, and the CLI half of the plan's cited evidence is simply
false.

## Empirical repro 2: line coverage does not export an artifact via the runner path

```
$ SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=/tmp/cov.sdn \
    bin/simple test --coverage --no-cache <a real branching spec>
...
2 passed
coverage: SIMPLE_COVERAGE set; bypassing test daemon
$ ls /tmp/cov.sdn
ls: cannot access '/tmp/cov.sdn': No such file or directory
```

The run completes and passes, and prints the one banner line confirming the
env var was read (`test_runner_client.spl:368-398`'s "bypassing test daemon"
message) — but no coverage artifact appears anywhere: not at
`SIMPLE_COVERAGE_OUTPUT`, not the per-target `coverage: <path> NN%` stdout
lines the wm_gui_web plan's §1.2/§3.2 describes and depends on for its
baseline unit (U1.2) and closure wave (U4.x). This means the wm_gui_web plan's
characterization of line coverage as the working "real primitive" is **too
generous** — the primitive that actually reproduces end-to-end (artifact or
percent line, from the `.spl`/spipe test-runner path an executing agent would
actually use) is not yet demonstrated. It may still work through a narrower
path (direct Rust-seed unit test of the collector, not exercised here); this
doc makes no claim about that path, only about the spipe/.spl runner path
every coverage plan unit in this repo is written against.

## Stale-artifact evidence

The only coverage artifact anywhere in the tree, `build/coverage/coverage.sdn`,
is stale (mtime 2026-08-02, four days old at time of writing) and contains a
branch-shaped schema (`decisions`/`conditions` tables) with **zero rows** and
`total_decisions: 0` — consistent with "never populated by a real run," not
"recently produced by the repro above."

## Structural root causes (traced file:line, not guessed)

1. **Production MIR lowering never calls the coverage-instrumented lowering
   path.** `src/compiler_rust/compiler/src/mir/lower/lowering_coverage.rs:15-39`
   emits `DecisionProbe`, correctly gated on `coverage_enabled` — but the
   production compile path calls the plain, non-coverage
   `mir::lower_to_mir(&hir)` at
   `src/compiler_rust/compiler/src/pipeline/execution.rs:993`. The
   coverage-instrumented variant, `lower_to_mir_with_coverage`
   (`src/compiler_rust/compiler/src/mir/lower/mod.rs:101`), is called **only**
   from Rust unit tests
   (`src/compiler_rust/compiler/src/mir/lower/tests/branch_coverage/helpers.rs:15`).
   Consequence: **JIT and native codegen emit zero branch probes**, regardless
   of `SIMPLE_COVERAGE`.
2. **Even where decisions ARE recorded (interpreter), file/line identity is
   fabricated, so per-file/per-module rollup is structurally impossible, not
   merely unverified.** The interpreter's own decision-recording call sites
   (`src/compiler_rust/compiler/src/interpreter_call/core/interpreter_control.rs:279,317,443,484,516,4741`)
   hardcode the source file as the literal string `"<source>"`. MIR probe
   construction sites separately hardcode `line=0, column=0`
   (`src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs:1074,1292,1443,1882`;
   `src/compiler_rust/compiler/src/mir/lower/lowering_expr_ops.rs:40`). No
   amount of re-running the collector recovers a real file:line from these
   sites — the identity information needed for "coverage % of file X" is
   never captured in the first place.
3. **The `.spl`-side coverage extern is a no-op stub under the interpreter.**
   `src/lib/nogc_sync_mut/io/coverage_simple.spl:71,88` calls through to
   `src/compiler_rust/compiler/src/interpreter_extern/coverage.rs:590-596`,
   which is a stub that does nothing.
4. **The seed's own collector hardcodes zero branch totals.**
   `src/compiler_rust/compiler/src/coverage.rs:178-179` sets
   `branches_hit: 0, branches_total: 0` unconditionally — matching the stale
   `build/coverage/coverage.sdn` artifact's `total_decisions: 0` exactly.
5. **Export never fires on the spipe/.spl runner path.** `save_coverage_data`
   (`src/compiler_rust/driver/src/cli/test_runner/coverage.rs:8`) is called
   from `runner.rs:434` — but the spipe/.spl runner path used by every
   `bin/simple test` invocation (confirmed in empirical repro 2 above,
   `coverage: SIMPLE_COVERAGE set; bypassing test daemon` — note "bypassing")
   does not reach that call site, so `save_coverage_data` never runs for a
   `.spl` spec run this way.
6. **The C-side collector is linked from the wrong tree for this path.**
   `src/runtime/runtime_coverage_core.c` self-describes at line 1 as
   "for the core-c-bootstrap bundle," but the seed links
   `src/compiler_rust/runtime/src/coverage.rs:190,213` instead — a second,
   independent reason the C probes referenced by the wm_gui_web plan's §1.2
   (`rt_coverage_decision_probe`/`rt_coverage_condition_probe`,
   `src/runtime/runtime_coverage_core.c:127-134`) are not the code path
   actually exercised by `bin/simple test`.

## Why "~100% branch/line coverage" is not currently a meaningful target

Five prerequisites need to land before a coverage percentage — branch or
per-module line — means what it appears to say. Any future coverage-closure
plan should treat these as blocking, in-scope prerequisite units, not
background assumptions:

1. **Real source spans in probe call sites** — replace the hardcoded
   `"<source>"` file identity (interpreter_control.rs) and hardcoded
   `line=0, column=0` (lowering_stmt.rs, lowering_expr_ops.rs) with the actual
   file/line/column of the decision site.
2. **Wire `set_coverage_enabled` through to `lower_to_mir_with_coverage` in
   the production path** — today only Rust unit tests reach it; JIT/native
   codegen must call it too, gated the same way, or JIT/native coverage stays
   permanently zero.
3. **Implement the `spl-coverage` subcommand in the deployed binary** —
   `src/app/spl_coverage/main.spl` exists as source but is not reachable from
   `bin/simple`; needs real dispatch-table wiring, not just a source file.
4. **Wire coverage export into the spipe/.spl runner path** — `runner.rs:434`
   → `save_coverage_data` is the working call chain today, but the actual
   `bin/simple test <spec>` invocation an agent runs does not go through it
   (repro 2 above); either route the spipe/.spl runner through that chain or
   build an equivalent export call on the path it does use.
5. **Build a rollup computing taken/not-taken per site** — even once spans
   and export both work, nothing today aggregates raw decision events into a
   per-file or per-module hit/total table; this is new code, not a
   configuration fix.

## Correction required in two landed plans

- `doc/03_plan/ui/testing/render_2d_vulkan_functional_coverage_plan_2026-08-07.md`
  §"Investigation findings" item 4 and Wave-1 Unit B1 assumed a working
  `spl-coverage` CLI. Corrected 2026-08-07 to note the CLI does not exist in
  the deployed binary and to make instrumentation-bring-up an explicit
  prerequisite unit blocking B1/C1-C3, referencing this bug doc.
- `doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md`
  §1.2 characterized line coverage as "REAL" (branch coverage as inert, citing
  the sibling 2026-08-02 bug). Corrected 2026-08-07: line coverage does not
  reproduce end-to-end via the spipe/.spl runner path either (repro 2 above);
  U1.2/U1.3/Wave-4 updated to make U1.3 an explicit "build the primitive"
  blocking unit, referencing this bug doc.

## Standing-rule note

This is a direct instance of the repo's own standing rule: **measure the
primitive before building on a derived signal**
(`feedback_measure_the_primitive_before_building_on_a_derived_signal.md`).
Both plans cited a CLI/pipeline as working evidence without running it; a
five-minute empirical repro (the two commands above) disproved both claims.
