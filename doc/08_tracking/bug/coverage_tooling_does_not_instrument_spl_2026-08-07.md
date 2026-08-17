# Coverage tooling does not reproduce end-to-end — no `spl-coverage` CLI in the deployed binary, no branch probes emitted by production MIR lowering, and no coverage artifact written by the spipe/.spl test-runner path

- **Date:** 2026-08-07
- **Severity:** high (planning-blocking) — two landed 2026-08-07 coverage plans
  (`doc/03_plan/ui/testing/render_2d_vulkan_functional_coverage_plan_2026-08-07.md`,
  `doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md`)
  built branch-coverage and line-coverage closure units on top of tooling that
  does not currently work end-to-end. No product functionality is broken by
  this; it blocks trustworthy coverage MEASUREMENT, both branch and line.
- Status: OPEN (P2) — **blocker cleared, end-to-end still unverified**
- Status re-verified 2026-08-17 by source inspection (independent
  re-verification pass). Deliberately NOT closed. What changed is the caveat
  recorded in the fourth-pass section below, not the defect:
  - That caveat said prereqs 1 and 2 depended on Rust seed source that was
    "uncommitted local working-copy state, not yet landed". That is no longer
    true. `src/compiler_rust/compiler/src/interpreter_extern/coverage.rs` is
    tracked and committed (`git log -1` -> `ae55a7467197`), and
    `git status --porcelain` reports it clean against HEAD.
  - The `spl-coverage` CLI is registered in the deployed driver:
    `src/compiler_rust/driver/src/main.rs:963-966` declares
    `name: "spl-coverage"` -> `app_path: "src/app/spl_coverage/main.spl"`, and
    it appears in the command dispatch list at `main.rs:310`
    (alongside `coverage` :309 / `main.rs:952`).
  - So the specific *blocker* this record names — no such CLI, and the
    supporting seed source not landed — is gone.
  - **Still unverified, which is why this stays OPEN:** no coverage run was
    executed in this pass, so nothing here establishes that MIR lowering
    actually emits branch probes or that the spipe/`.spl` test-runner path
    writes a coverage artifact. Registering a subcommand is not the same as the
    export working end to end, and that end-to-end claim is the substance of
    this bug.

  **Verified by source inspection only.**
  the "Gate rebuilt with real mechanical probes for all 5 prerequisites
  (fourth pass)" section near the end of this doc,
  `check-render2d-coverage.shs` mechanically probes all five prerequisites
  (no more placeholder/UNVERIFIED-BY-SCRIPT rows) and the current verdict,
  reproduced twice for stability, is **PASS — 5 prerequisite(s) checked, all
  met**. Read the fourth-pass section's caveat before relying on this: the
  MET result for prereqs 1 and 2 depends on Rust seed source
  (`interpreter_extern/coverage.rs`, `coverage.rs`) that is currently
  **uncommitted local working-copy state**, not yet landed on `origin/main`
  — a clean rebuild from `origin/main` alone would very likely revert those
  two rows to UNMET until that source lands as a real commit. This doc is
  therefore left open (not closed) pending that commit. Earlier history below
  (original filing, "Correction," "Unit B1 execution note," "Unit C2/C3
  assessment") is preserved as-is per this repo's append-don't-rewrite
  convention; treat the fourth-pass section as the current state.

## 2026-08-08 ML-KEM coverage retry

`SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<fresh /tmp path> bin/simple test
test/01_unit/os/crypto/x25519mlkem768_absolute_spec.spl --coverage --no-cache`
reached the runner's `coverage: SIMPLE_COVERAGE set; bypassing test daemon`
marker but produced neither a spec verdict nor the requested artifact. The
first attempt exposed and then fixed a missing pure-Simple `os.crypto.entropy`
facade; the next two attempts still ended at the coverage bypass, including
after the generated epilogue was changed to use the canonical named-dump
function form. This is therefore a runner execution/export failure, not
evidence of zero ML-KEM outcomes. The three-cycle limit was reached; retain
the raw logs under `/tmp/x25519mlkem768_absolute_coverage*.log` for diagnosis
and do not claim a measured receipt from them.

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

### 2026-08-08 incremental-redeploy diagnostic

The source-side coverage epilogue repair (`f9e45226dd5`) was newer than the
deployed `bin/simple`: the deployed CLI timestamp was 2026-08-08 12:14 UTC,
while the repair landed at 15:19 UTC. Therefore the no-SDN/no-verdict ML-KEM
attempt executed an old runner that injected raw top-level prints rather than
the callable dump function. An isolated incremental Stage-2 native-build
attempt also exited zero without producing its requested output artifact, so it
cannot redeploy the repair. This is an explicit compiler/build defect, not
coverage evidence. Current source now fails closed when a coverage child lacks
dump sentinels; a fresh provenance-qualified self-hosted redeploy is still
required before retrying measured ML-KEM coverage.

### 2026-08-08 direct-source runner attempt

To eliminate the stale deployed single-runner as the only explanation, the
current `src/app/test_runner_new/test_runner_single.spl` was run directly with
`SIMPLE_COVERAGE=1`, a fresh `SIMPLE_COVERAGE_OUTPUT` path, and
`x25519mlkem768_absolute_spec.spl`. It printed the selected child binary but
then produced neither a spec verdict nor an SDN artifact. The output also
reported `rt_file_is_char_device` as an unresolved JIT external and fell back
to the interpreter. This route did not reach the source fail-closed sentinel
check, so it is a lower child-execution failure. It is not coverage evidence;
do not rerun the same command until the child runner emits a bounded diagnostic
or self-hosted artifact execution is restored.

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

## Unit C2/C3 assessment 2026-08-07 (third pass) — branch export has NO denominator, and the collector emits no branch data at all

Tasked with assessing whether Wave 3 units C2 (`src/lib/nogc_sync_mut/gpu/engine2d/`
closure) and C3 (`src/os/compositor/` engine2d+software+vulkan closure) are now
achievable, given that the same-day commits `ae97a34cd365`, `736d741ff68e`,
`70907278997d`, `9c5bcf074498`, `4ee7a8f47f08` landed real export, CLI dispatch,
app imports, cross-process `--file` load, and real file identity on decision
probes. **Verdict: NOT achievable — on two independent axes, not one.**

### Axis 1: branch/decision data is structurally absent from the exported artifact (deeper than the known line:0/column:0 gap)

Ran the real acceptance flow with the locally-built binary
(`src/compiler_rust/target/release/simple`, confirmed non-seed-warning build
containing all five 2026-08-07 fixes):

```
SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=/tmp/c3_cov_test2.sdn \
  src/compiler_rust/target/release/simple test \
  test/01_unit/os/compositor/engine2d_damage_report_spec.spl --no-cache --no-cover-check
```
Verdict line: `Results: 7 total, 7 passed, 0 failed`. Artifact written,
22275 bytes non-empty, real per-line paths (e.g.
`/home/ormastes/dev/pub/simple/src/lib/gc_async_mut/gpu/engine2d/backend_software.spl, 1413, 1`).

But the artifact has **only two sections**: `lines |file, line, hit_count|` and
`functions |name, call_count|`. There is no `branches` or `decisions` section
at all, and `summary:` reports `total_functions: 37` / `covered_functions: 37`
and `total_lines: 396` / `covered_lines: 396` — i.e. `covered == total`
identically, which is what the collector always emits, not a measured 100%.

Root cause, traced to source (this binary's build, matches origin/main at
fetch time):
- `src/compiler_rust/compiler/src/coverage.rs:79-84` — `CoverageCollector`
  has three fields: `line_hits`, `function_calls`, `sffi_calls`. No decision/
  branch field exists on the struct that backs `to_sdn()`.
- `src/compiler_rust/compiler/src/coverage.rs:109-149` (`to_sdn`) — emits
  `lines`, `functions`, optional `sffi_calls`, and `summary`. No branches
  section is ever written, structurally — there is no code path that could
  emit one.
- `src/compiler_rust/compiler/src/coverage.rs:170-181` (`stats()`) —
  `total_lines = self.line_hits.values().map(len).sum()`,
  `lines_hit: total_lines` (same value twice); `total_functions =
  self.function_calls.len()`, `functions_hit: total_functions` (same value
  twice); and `branches_hit: 0, branches_total: 0` hardcoded. The collector
  records only HITS — nothing enumerates a file's total executable lines/
  functions/branches, so "coverage" here is 100%-by-construction for any run,
  not a measured ratio. **No percentage can be computed from this artifact,
  for lines or branches — do not report one.**
- `src/compiler_rust/compiler/src/interpreter_extern/coverage.rs:590-597` —
  `rt_coverage_decision_probe_fn` and `rt_coverage_condition_probe_fn` (the
  interpreter-path entry points, i.e. what `bin/simple test` actually calls)
  are literal no-op stubs: `Ok(Value::Nil)`. Even where the interpreter's six
  decision-probe call sites now pass a real file path (per `4ee7a8f47f08`),
  the receiving function on the interpreter path discards it.
- Contradiction to flag: `coverage.rs:3-4`'s module comment claims "Runtime
  decision/condition probes live in simple_runtime and are merged when
  saving" — no merge step exists anywhere in `to_sdn()` or `stats()`. That
  comment is aspirational, not descriptive, as of this build.
- `src/app/spl_coverage/main.spl` — confirmed unchanged from origin/main
  (byte-identical `diff`), dispatch has only `dump`/`status`/`clear`
  (lines 176/178/199). No `report --filter` rollup subcommand exists, so
  even if branch data existed in the artifact there is no per-file
  functions/branches rollup command for C1-C3's acceptance flow to pipe into.

So the C2/C3 acceptance command
(`bin/simple spl-coverage dump | <B1 report filter> <path-prefix>`) cannot
identify "remaining uncovered arms" for two independent reasons: the
`report --filter` half doesn't exist, and even a hand-rolled substitute has
no branch rows to filter — the collector never captures them past a no-op
stub, and the exporter has no schema slot for them if it did.

### Axis 2: the corresponding Wave 2 units are unlanded (plan's own dependency, unmet regardless of B1)

The plan states "Wave 3 depends on B1 (measurement) and the corresponding
Wave 2 unit per module." Checked against `origin/main` directly
(`git ls-tree origin/main -- <path>`, not the stale local WC):

- F7 (`simd_native_rows.spl` closure) spec
  `test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_native_rows_spec.spl` —
  **absent from origin/main** (empty `git ls-tree` result).
- F8 (`compositor_engine2d.spl` surface closure) spec
  `test/01_unit/os/compositor/compositor_engine2d_surface_spec.spl` —
  **absent from origin/main** (empty `git ls-tree` result).
- F6's target spec `test/01_unit/lib/gpu/engine2d/simd_kernels_spec.spl` does
  exist (blob `abb0ce4...` in origin/main), so F6 is at least startable, but
  C2 spans both F6- and F7-covered source files, so C2 is still gated on F7.

This means C2 and C3 would stay blocked even if B1's branch-export gap were
fixed today — they are additionally blocked on Wave 2 prerequisite units that
have not landed. This closes the "is it purely a deploy dependency" question:
it is not; it is two unmet prerequisite units plus a real primitive gap, none
of which this pass fabricated a workaround for.

### What was NOT done, and why

No spec was added for C2 or C3's target files. Writing "closure" `it` blocks
against branch arms requires knowing which arms are uncovered; the only
available signal (line hits) reports covered==total by construction (see
Axis 1), so any such spec would be closing arms selected by guesswork, not by
measurement — exactly the fail-open shape this doc exists to prevent. No gate
script or CLI subcommand was edited to force a flip, per this plan's own
explicit prohibition against editing `check-render2d-coverage.shs` to fabricate
a pass.

**C2 status: NOT achievable this pass. Unblock condition:** (a) F7's spec
lands (Wave 2 prerequisite), AND (b) branch/decision data gets a real field on
`CoverageCollector`, a real emission block in `to_sdn()`, real per-branch
hit/total accounting in `stats()` (not hardcoded zero), and the interpreter's
`rt_coverage_decision_probe_fn`/`rt_coverage_condition_probe_fn` stop being
no-ops — four concrete Rust-side changes, all in
`src/compiler_rust/compiler/src/coverage.rs` and
`src/compiler_rust/compiler/src/interpreter_extern/coverage.rs`.

**C3 status: NOT achievable this pass. Unblock condition:** (a) F8's spec
lands (Wave 2 prerequisite), AND (b) same four branch-export changes as C2
(shared primitive, not a per-unit gap).

Neither unit's blocker is the deployed-binary gate
(`check-render2d-coverage.shs`) — both are blocked upstream of it, on the
collector/exporter itself and on unlanded Wave 2 specs. Fixing the deploy
would not unblock either unit today.

## Gate rebuilt with real mechanical probes for all 5 prerequisites (2026-08-07, fourth pass)

`scripts/check/check-render2d-coverage.shs` previously probed prerequisites 3
and 4 mechanically and recorded 1, 2, 5 as permanent placeholder UNMET rows
("not mechanically probed ... treated as unmet until re-verified"). This pass
replaced every row with a real probe against the live deployed binary
(`bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`, rebuilt
2026-08-07 22:59) and fixed a bug in the prereq-3 probe itself:

- **Prereq 3 probe bug fixed:** the old probe ran `bin/simple spl-coverage
  status` with `SIMPLE_COVERAGE` unset and treated its exit 1 as failure —
  but exit 1 there is documented, correct behavior ("Coverage tracking is
  DISABLED"), not a dispatch failure. Fixed to run with `SIMPLE_COVERAGE=1`
  and check for the actual failure signature (`file not found:
  spl-coverage`) instead of conflating "coverage disabled" with "subcommand
  absent."
- **Prereq 1 and 2 probe redesigned mid-pass** after review flagged that the
  first version (inspecting a `bin/simple test --coverage` artifact) could
  not distinguish "the interpreter recorded a decision" from "MIR lowering
  emitted a real probe" — both an interpret-mode-forced run and the default
  `bin/simple test` run produced identical `total_decisions=57`, an
  inconclusive A/B. Replaced with a probe that compiles a tiny self-contained
  branching `.spl` file through `bin/simple compile --emit-mir=<path>`
  twice — once with `SIMPLE_COVERAGE` unset, once with `SIMPLE_COVERAGE=1` —
  and inspects the MIR JSON directly, independent of both the interpreter and
  the test runner. Empirically: 0 `DecisionProbe` instructions unset, 1 with
  `SIMPLE_COVERAGE=1`, and the probe's own `file`/`line` Debug fields name
  the real compiled source path and a positive line number (not `<source>`
  or `0,0`).
- **Prereq 5** now runs the probe spec twice, rolls up both artifacts via
  `spl-coverage rollup`, and confirms a specific decision id's `true_count`
  in the merged output equals the sum of the two inputs' counts for that id
  (picked to be nonzero in both inputs, so a broken no-op merge landing on
  `0+0=0` cannot read as a false MET) — verified real per-site summation
  (e.g. `72 + 72 = 144`), not dedup or passthrough of one input.

**Current verdict (reproduced twice for stability):**
```
check-render2d-coverage: PASS — 5 prerequisite(s) checked, all met (branch-coverage % may be reported)
```
All five rows MET. Sabotage-verified fail-closed: (a) pointing the probe spec
at a nonexistent file correctly flips prereqs 1/2/4/5 to UNMET and the
verdict to FAIL; (b) a mutated copy that breaks prereq 2's env-gating check
(forces the "gated correctly" branch to `false`) correctly reports
`DecisionProbe emitted regardless of SIMPLE_COVERAGE (nocov=0, cov=1)` and
flips the overall verdict to FAIL.

### Important caveat: the underlying fix is currently UNCOMMITTED local WC state, not yet on origin/main

The deployed binary's prereq-1/2 MET result depends on
`src/compiler_rust/compiler/src/interpreter_extern/coverage.rs`'s
`rt_coverage_decision_probe_fn`/`rt_coverage_condition_probe_fn` no longer
being no-op stubs — confirmed by direct source read, they now forward to a
real runtime decision store. **This file, and
`src/compiler_rust/compiler/src/coverage.rs`, both show as locally modified
(`git status --porcelain`) with no matching commit on `origin/main`** as of
this pass; `CoverageCollector` itself (`coverage.rs:79-84`) still has no
decision/branch field and `stats()` (`coverage.rs:170-181`) still hardcodes
`branches_hit: 0, branches_total: 0` unchanged — the decision data flows
through a separate runtime store merged at dump time, not through
`CoverageCollector`. The deployed binary's mtime (22:59) postdates both
files' mtimes (16:52, 17:12), confirming the binary under test was built
from this uncommitted WC state, not from a clean `origin/main` checkout. This
pass did not touch, commit, or revert these two files — they belong to
in-flight work from a concurrent session/agent (see the shared-WC hazard
notes in this repo's standing rules) and are out of scope for a
shell-script-gate-only change. **Anyone rebuilding `bin/simple` from a clean
`origin/main` checkout today would very likely see prereqs 1 and 2 revert to
UNMET** until those two Rust files land as a real commit. The gate script
itself is correct and will catch that regression immediately if it happens —
this caveat is about the state of the Rust seed source, not the shell script.

### Relationship to the "Unit C2/C3 assessment (third pass)" section above

That section's Axis 1 (`CoverageCollector` has no decisions field,
`rt_coverage_decision_probe_fn` is a no-op stub) was accurate against the
binary it tested at the time. The uncommitted WC changes described above
supersede part of that finding for the interpreter-probe-forwarding half, but
`CoverageCollector`'s own schema is unchanged (still no decisions field, no
real branches/total accounting) — so Axis 1's core conclusion ("no
percentage can be computed from the `CoverageCollector`-only artifact, do not
report one") still stands for the `lines`/`functions` half of the SDN. The
`decisions` section this pass's probes rely on comes from the separate
runtime-store merge, not from `CoverageCollector.to_sdn()`. Axis 2 (Wave 2
prerequisite specs F7/F8 absent from `origin/main`) is unaffected by
anything in this pass and still blocks C2/C3 regardless. **This pass does
not reopen or re-assess C2/C3 achievability** — it only rebuilds the
render_2d Wave-3 prerequisite gate script itself, per its own scope.

## 2026-08-15: per-file branch summary line landed (prerequisite 5's rollup, runner path)

Minimal end-to-end slice implemented in pure Simple (no rebuild needed —
runner source is read at process start):
`src/app/test_runner_new/test_runner_single.spl`'s `_cov_print_report` now
also parses the runtime store's `decisions |id, file, line, column,
true_count, false_count|` section of the merged SDN and prints, per `@cover`
target, alongside the existing line banner:

```
coverage-branch: <path> NN% (hit/total decisions)
```

A decision counts as hit when BOTH outcomes were taken. **Denominator
semantics, stated honestly:** total = decisions the run actually EXECUTED in
that file (the runtime store records nothing for never-reached decisions), so
this is decision-outcome coverage over executed decisions, not over all
static decisions in the file. A static denominator (enumerate all decisions
via MIR probe-plan of the target file) remains future work, as does JIT/
native probe emission on the production `lower_to_mir` path (root cause 1)
— this slice covers the interpreter path `bin/simple test` actually uses.

Verification (2026-08-15, `bin/simple` -> Rust seed
`bin/release/x86_64-unknown-linux-gnu/simple`): a 3-example branching spec
with `# @cover src/lib/common/base_encoding.spl`, run as
`SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<path> bin/simple test <spec>
--coverage --no-cache --no-cover-check`, printed
`Results: 3 total, 3 passed, 0 failed`, wrote a 6,719-byte SDN artifact whose
`decisions` section holds 10 real `src/lib/common/base_encoding.spl` rows
(real line/column, nonzero true/false counts), and emitted
`coverage: src/lib/common/base_encoding.spl 55% (29/52 lines)` plus
`coverage-branch: src/lib/common/base_encoding.spl 40% (4/10 decisions)` —
the 4/10 hand-checked against the artifact rows (exactly 4 rows have both
counts > 0). Branch coverage is now measurable on the spipe/.spl runner
path, with the executed-decisions denominator caveat above.

## 2026-08-15 — coverage-branch verified on a real integration spec

`SIMPLE_COVERAGE=1 ... bin/simple test test/02_integration/rendering/wm_api_vs_ir_pixel_parity_spec.spl --coverage --no-cache --no-cover-check` (Rust seed, load ~3):

```
Results: 2 total, 2 passed, 0 failed
coverage: src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl 13% (162/1170 lines)
coverage-branch: src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl 4% (2/46 decisions)
coverage-branch: src/lib/gc_async_mut/gpu/engine2d/engine.spl 0% (0/39 decisions)
```

The reporter works end-to-end on arbitrary @cover-annotated specs. The
"overall 80% branch coverage" target for wm/gui/web/engine2d is now
MEASURABLE; reaching it is the campaign tracked by
doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md and
render_2d_vulkan_functional_coverage_plan_2026-08-07.md — this measurement is
the honest baseline, not the target.

## 2026-08-15 — per-layer 80% branch-coverage campaign results (parallel agents)

Flagship-module decision coverage, all specs green, measured via the
coverage-branch reporter landed earlier this session:

| Layer | Module | Decisions | Verdict |
|---|---|---|---|
| 2d (draw path) | gpu/engine2d/draw_ir_adv.spl | 80% (124/155) | 22/22 |
| gui | ui/render_opt/damage_plan.spl | 93% (15/16) | 34/34 |
| gui | ui/render_opt/damage_tiles.spl | 95% (40/42) | (same spec) |
| web | browser_engine/web_draw_ir_damage_consumer.spl | 80% (4/5) | 12/12 |
| vulkan | os/compositor/vulkan_present_damage_gate.spl | 100% (9/9) | 14/14 |
| wm | os/compositor/engine2d_wm_frame_executor.spl | campaign in flight | — |

Remaining one-sided decisions per module are catalogued in each spec/agent
report as provable headless ceilings (device/FFI lanes, never-nil retained
engines, compile-time-false probes). Struct-method attribution gap filed as
coverage_probe_plan_skips_struct_method_decisions_2026-08-15.md.

## Evidence 2026-08-17 (fleet worker A, rust-seed slice)

Content check confirms the doc's own caveat is still accurate:

- `spl-coverage` exists **only** as a driver CLI arm —
  `src/compiler_rust/driver/src/main.rs:310` (dispatch), `:963-966`
  (`app_path: "src/app/spl_coverage/main.spl"`), `:1368`, `:1497`.
- `lowering_coverage` is referenced only by `mir/lower/mod.rs:9` and its own
  tests (`mir/lower/tests/branch_coverage/{misc.rs:375,expr.rs:407}`) — no
  production wiring to the `.spl` runner artifact path.

**Verdict: STILL-OPEN, confirmed by content.** Same family as
`coverage_probe_plan_skips_struct_method_decisions_2026-08-15.md`; both are the
same missing-instrumentation cause and should be tracked together.
**Not proven:** no execution evidence — see "Execution blocked" below.
