# Coverage tooling does not reproduce end-to-end — no `spl-coverage` CLI in the deployed binary, no branch probes emitted by production MIR lowering, and no coverage artifact written by the spipe/.spl test-runner path

- **Date:** 2026-08-07
- **Severity:** high (planning-blocking) — two landed 2026-08-07 coverage plans
  (`doc/03_plan/ui/testing/render_2d_vulkan_functional_coverage_plan_2026-08-07.md`,
  `doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md`)
  built branch-coverage and line-coverage closure units on top of tooling that
  does not currently work end-to-end. No product functionality is broken by
  this; it blocks trustworthy coverage MEASUREMENT, both branch and line.
- **Status:** open, PARTIALLY RESOLVED. Structural root causes pinned by
  source read (file:line below). Prerequisite 4 (export) landed in commit
  `ae97a34cd365` ("fix(test-runner): export coverage SDN to
  SIMPLE_COVERAGE_OUTPUT (U1.3 prereq 4)") — `check-render2d-coverage.shs`
  row `prereq4_artifact_export` now reads MET; see the "Correction" section
  below. Prerequisites 1 (partially), 2, 3, 5 remain unmet. Overall gate
  verdict is still FAIL.

## Correction 2026-08-07 (later pass, after `ae97a34cd365`)

Two claims in this doc, as originally written, no longer hold and are
corrected here rather than rewritten in place (repo convention: append, don't
silently rewrite a bug doc's history):

1. **Prerequisite 4 (export) is now MET, not "still unmet exactly as
   documented."** `test_runner_single.spl` now writes `cov_sdn` to
   `SIMPLE_COVERAGE_OUTPUT` (guarded on the env var and non-empty data) —
   verified independently in this pass: an artifact 15,688-45,747 bytes
   across several runs, `# Coverage Report` header, real `(file, line,
   hit_count)` rows keyed on genuine `src/...` paths, matching the stdout
   `coverage: <path> NN%` banner exactly. `check-render2d-coverage.shs`
   confirms this mechanically (`prereq4_artifact_export -- artifact written
   and non-empty`).
2. **Prerequisite 1's framing ("the interpreter hardcodes file as
   `<source>`, line/col 0,0") is too broad as a description of LINE
   coverage.** That hardcoding is real but applies to the raw
   *decision/branch*-probe call sites (`interpreter_control.rs:279` etc.,
   feeding `rt_coverage_decision_probe`/branch coverage — still genuinely
   `<source>`/`0,0`, prerequisite 1 stays UNMET for branch coverage). LINE
   coverage uses a separate, already-working mechanism
   (`CURRENT_EXEC_MODULE`, documented at `test_runner_single.spl:345-386`):
   an **imported module's** statements inside functions are attributed to
   their own real file and line today, not to `<source>` or `<entry>`. Only
   an imported module's *top-level* statements (bounded, <=2 lines/module)
   still get mis-filed under `<entry>`; that residual is separately tracked
   and does not affect production modules exercised primarily through their
   functions (as `src/os/compositor/**`,
   `src/lib/gc_async_mut/gpu/browser_engine/**`, and `src/lib/common/ui/**`
   are, from a spec's perspective). U1.2's baseline
   (`doc/09_report/ui/testing/wm_gui_web_coverage_baseline_2026-08-07.md`)
   demonstrates this empirically: 16 real `coverage: <path> NN%` lines
   across all three module families, cross-checked against artifact bytes,
   plus a sabotage run (misspelled target) that correctly produced no line.
   **This correction is scoped to LINE coverage only** — branch coverage's
   `<source>`/`0,0` hardcoding is unaffected and prerequisite 1 stays UNMET
   for that axis, which is why the gate's overall verdict is still FAIL.

Everything else in this doc (prerequisites 2, 3, 5; the branch-coverage
scope; the "why ~100% branch/line coverage is not currently a meaningful
target" framing for BRANCH coverage specifically) is unchanged and still
accurate.

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
4. **MET (2026-08-07, commit `ae97a34cd365`).** ~~Wire coverage export into
   the spipe/.spl runner path~~ — `test_runner_single.spl` now writes
   `cov_sdn` to `SIMPLE_COVERAGE_OUTPUT` directly on the spipe/.spl runner
   path (not via `runner.rs:434`/`save_coverage_data`, which remains a
   separate, still-unused chain for this path). Gate-confirmed
   (`prereq4_artifact_export` MET); see "Correction 2026-08-07" above and
   `doc/09_report/ui/testing/wm_gui_web_coverage_baseline_2026-08-07.md`.
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

## Unit B1 execution note (2026-08-07, second pass)

Re-verified both repros empirically before doing any work (binary provenance:
`readlink -f bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`).
Both hold:

- `bin/simple spl-coverage status` -> `error: file not found: spl-coverage`
  (prerequisite 3 still unmet).
- `SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=/tmp/cov.sdn bin/simple test
  test/01_unit/lib/common/gpu/engine2d/scalar_oracle_spec.spl --coverage
  --no-cache` prints `38 total, 38 passed, 0 failed` and then two per-file
  **line**-coverage banners (`coverage: src/lib/common/gpu/engine2d/scalar_oracle.spl
  89% (95/106 lines)`, likewise for `kernel_registry.spl`) with real file
  identity — so line-percent-with-real-path on stdout does work today, more
  than repro 2's original text implied. But no artifact is ever written at
  `SIMPLE_COVERAGE_OUTPUT`, and `build/coverage/coverage.sdn` stays untouched
  (still the stale 2026-08-02 zero-decision file) — prerequisite 4 (export)
  is still unmet exactly as documented, and this doc's characterization of
  prerequisite 4 stands.

  **STALE as of the later pass documented in "Correction 2026-08-07" above:**
  commit `ae97a34cd365` landed the missing write to `SIMPLE_COVERAGE_OUTPUT`
  after this note was written. Prerequisite 4 is now MET (gate-confirmed).
  `build/coverage/coverage.sdn` staying untouched is expected and not a
  counter-signal — that path is the *unrelated* Rust-seed `--native`
  collector output (branch-shaped schema, prerequisite 2/5 territory), not
  the `SIMPLE_COVERAGE_OUTPUT` path this note and prerequisite 4 are about.

Per the plan's own reframing, B1 cannot build all five prerequisites in one
unit (prerequisite 1 alone requires editing ~10 pinned Rust seed call sites
across `interpreter_control.rs`, `lowering_stmt.rs`, `lowering_expr_ops.rs`
to stop hardcoding `"<source>"` / `line=0,column=0`; prerequisites 2 and 5 are
comparable-sized MIR/export work). Rather than wire prerequisite 3 alone
(which would make a CLI subcommand answer with fabricated/zero data and look
more "done" than the current honest `file not found` error — the exact
fail-open shape this doc warns against), this pass built a fail-closed gate:
`scripts/check/check-render2d-coverage.shs`. It probes prerequisites 3 and 4
directly against the live binary and records 1/2/5 as unmet pending a future
mechanical probe (grepping the pinned Rust sites), never silently skipping
them. Verdict format matches `check-tree-size-push.shs`
(`PASS —`/`FAIL —`/`ERROR —`, last stdout line, exit 0/1/2). Sabotage-verified
in a scratch `git worktree`: a fake `bin/simple` that fabricates prerequisites
3+4 (prints `status: ok`, writes a dummy artifact) flips exactly those two
rows to MET while 1/2/5 stay UNMET and the overall verdict stays FAIL — the
gate does not fabricate a PASS. Current real-repo run: **FAIL — 5
prerequisite(s) checked, 5 unmet.**

**Unit B1 status: NOT done.** None of the five prerequisites landed this
pass; C1-C3 remain blocked. What did land: a re-verified, current repro of
both empirical claims above (with the line-coverage-banner correction noted),
plus the fail-closed prerequisite gate other units/agents can run instead of
re-deriving "is coverage measurement trustworthy yet" from prose each time.

## Standing-rule note

This is a direct instance of the repo's own standing rule: **measure the
primitive before building on a derived signal**
(`feedback_measure_the_primitive_before_building_on_a_derived_signal.md`).
Both plans cited a CLI/pipeline as working evidence without running it; a
five-minute empirical repro (the two commands above) disproved both claims.
