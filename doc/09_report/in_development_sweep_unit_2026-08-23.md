# In-development tag sweep — slice 1: `test/01_unit/` + `test/unit/`

Date: 2026-08-23. Mechanism: `@tag:in-development` (`970920e02cd`,
`src/lib/nogc_sync_mut/spec/in_development.spl`).
Binary: `bin/release/x86_64-unknown-linux-gnu/simple` (Rust bootstrap **seed** —
it self-identifies with the seed banner; no full-CLI pure-Simple binary is
deployed, so every verdict below is a SEED verdict).
Worktree: `/mnt/fast/wt-tagsweep-unit` at `276330545f7`.

## Headline: the slice as scoped is not executable on this box

This is the load-bearing finding, so it is stated before the counts.

| quantity | measured |
|---|---|
| specs in `test/01_unit/` | 8,713 |
| specs in `test/unit/` | 5,229 |
| `test/unit/` specs **byte-identical** to their `test/01_unit/` twin | 4,484 |
| `test/unit/` specs with no twin or a divergent twin | 745 |
| **distinct specs that must actually be executed** | **9,458** |
| measured cost per spec (5-file batch, warm, shared box) | **~18.5 s** |
| implied serial cost | **~48 hours** |

The 4,484 byte-identical mirror specs are the one real saving: their verdict is
inherited from the `test/01_unit/` twin by construction, which is also what keeps
`scripts/check/check-test-tree-divergence.shs` green when a tag is applied — a
tag must land on BOTH members of an identical pair or it creates divergence.

Batching many spec paths into one `simple test` invocation does **not** amortise:
the runner re-execs per file (`simple test --no-session-daemon --timeout 900
<one spec>` per file, visible in `ps`), so the ~12 s stdlib-load cost is paid per
spec no matter how the invocation is shaped. Measured: 1 file 12.2 s; 3 small
files 19.4 s; 5 representative files 92.9 s.

Concurrency could not be used to close the gap. The box is shared: this session
began at load 44 with 19 GB free, a sibling lane (`run17`) had already been
OOM-killed three times at ~16 GB free, and the coordinator throttled this sweep
from 2 concurrent jobs to **1, with a pause whenever available memory drops
below 15 GB**. That is the correct trade — losing the in-flight stage1 build
costs an hour of measurement, losing sweep throughput costs only time — but it
means full coverage of this slice is a multi-day job, not a session job.

**Consequence:** the counts below describe a *stratified sample*, not the tree.

## Method

1. The recorded DB was not used. `doc/08_tracking/test/test_result.md` reports
   Total 770 / Passed 0 / Failed 0 and `test_db.sdn`'s file→name joins are wrong
   (`doc/08_tracking/bug/test_db_incoherent_totals_and_broken_file_name_join_2026-08-23.md`).
2. Work set = 8,713 + 745 = 9,458 distinct specs, ordered **round-robin across
   directories** rather than alphabetically, so that any prefix of the run is a
   breadth-first sample of the whole tree instead of a deep dive into `app/`.
3. Each batch runs under `SIMPLE_TIMEOUT_SECONDS=0` with a 900 s wall timeout.
   Only the per-file `Results: N total, N passed, N failed` line is read as the
   verdict. Exit status is taken from the command, never from a pipe. A batch
   that emits fewer `Results:` lines than it had files identifies the aborting
   file positionally; that file is recorded `ABORT` and its log kept.
4. Each failure is classified before any tag is applied. Only genuinely
   unfinished feature work is tagged. Regressions, specs correctly asserting a
   real defect, and environmental failures are left RED and listed.

## `@cover` preflight gate — audited, did NOT fire on this slice

A sibling sweep lane found that the runner's `@cover` annotation preflight
(`src/app/test_runner_new/test_runner_main.spl:268-282`) can abort a whole run
and report every spec as failed while still emitting a well-formed `Results:`
line — measured there as `Results: 587 total, 0 passed, 587 failed` in ~3 minutes
with zero specs executed. That would have made this lane tag healthy specs.

**Audited here; the gate did not fire on any unit-tree batch.** Every retained
batch log carries real per-file `SPEC FILE VERDICT ... executed=N passed=N`
lines, none carries `AFTER_RUN_0_files`, none carries `Time: 0ms`, and no run
exited `rc=3`. The reason appears to be invocation shape: this lane always
passes **explicit spec file paths**, never a directory, so the discovery-mode
preflight is not reached. **0 of the 50 results below are affected.**

The general lesson still stands and is adopted here: `Results:` is authoritative
for a VERDICT but is not proof that anything RAN. Cross-check
`SPEC FILE VERDICT` / `AFTER_RUN_<n>_files` / `Time:` before classifying.
A directory-shaped sweep of this tree must pass `--no-cover-check`
(`test_runner_args.spl:484`).

## Coverage actually achieved

| | count |
|---|---|
| specs executed and verdicted | **248** |
| of the 9,458-spec work set | **2.6 %** |
| green (`0 failed`) | 194 |
| failing | 53 |
| tagged `@tag:in-development` | **0** |
| left RED | 54 |
| inconclusive / hung / ABORT | 1 |

Throughput was ~18.5 s/spec at the start and then collapsed: the memory gate
required by the throttle (pause below 15 GB available) held the single worker
idle for roughly 30 consecutive minutes while a sibling stage1 build held ~27 GB
across 9 workers. One orphaned worker was found stuck re-running
`test/01_unit/app/compile/cli_compile_surface_spec.spl` and was reaped.

The stratified worker is left running detached on
`/mnt/fast/tagsweep/s3.lst` -> `/mnt/fast/tagsweep/o3.tsv`; a later lane can
resume from it rather than starting over.

## Resource self-protect watchdog — audited, did NOT truncate this slice

The runner also carries a system-wide resource watchdog (`test_runner_main.spl:369,412`,
`resource_limit_pct` default 75, sampled every 20 tests) that exits **42**
(`EXIT_RESOURCE_SHUTDOWN`) with `GRACEFUL SHUTDOWN INITIATED` and a
`Completed tests: 20` line. Because it samples the WHOLE box (106 of 125 GB held
by sibling lanes here), it fires regardless of this lane's own load, and its
output looks like a completed partial run.

**Audited here; it did not fire on any unit-tree batch.** Two independent proofs:

- No retained batch log of this lane contains `GRACEFUL SHUTDOWN`,
  `EXIT_RESOURCE_SHUTDOWN`, or a `Completed tests:` line. (The only hits under the
  scratch root are a sibling lane's `logs_selfprotect/test_03_system_*.log`.)
- **Structural, and stronger: 0 `ABORT` rows across all 50 results.** This lane's
  driver counts the `Results:` lines a batch emits and compares that to the number
  of files it was given; any short count is recorded as `ABORT` and its log kept.
  A watchdog shutdown truncates the batch and therefore *must* produce a short
  count. Every batch emitted exactly as many `Results:` lines as it had files, so
  nothing was truncated.

**Summary of the three known ways this tree reports things that did not happen,
as they apply to this slice: incoherent DB — not used at all; `@cover` phantom
failures — did not fire (explicit file paths); resource-shutdown truncation — did
not fire (0 ABORT rows). All 50 results stand.** A directory-shaped sweep of this
tree needs `--no-cover-check --no-self-protect` and must still cross-check
`Completed tests:` against the unit's spec count.


### 3-9. Second harvest — seven more failures, still zero tagged

The sweep reached 63 specs. Every additional failure was triaged to a named
symbol or line, and **not one is unfinished feature work**. The recurring shape
is a spec that has drifted from a renamed or re-scoped implementation.

| spec | verdict | classification |
|---|---|---|
| `app/mcp/cli_passthrough_spec.spl` | 3/10 passed | **Rename drift.** Imports `_append_cli_args_for_name` from `app.mcp.cli_passthrough`; that module defines **`_cli_args_for_name`** (`src/app/mcp/cli_passthrough.spl:83`). The capability exists under the live name. |
| `app/dashboard/dashboard_serve_spec.spl` | 0/6 passed | **Visibility/import defect.** `_run_serve_result`, `_run_gui_result`, `_run_agents_result` all exist in `src/app/dashboard/dashboard_export_runtime.spl`; the spec cannot see them. Feature present. |
| `app/formatter/formatter_basic_spec.spl` | 1/2 passed | **Spec bug.** `expect(source).to_contain("Formatting failed for: {clean_file}")` — the `{clean_file}` inside the *expected literal* is interpolated, so it resolves as a variable and fails `variable clean_file not found`. The assertion needs escaping, not a feature. |
| `app/mcp/assistant/session_store_spec.spl` | 0/6 passed | **Ambiguous — left RED per the "when unsure" rule.** All six die on `cannot index value of type enum` at `session.children[0]` / `session.child_tasks[0]` (lines 134-148). Either the store getter returns an `Option`-shaped enum the spec never unwraps (spec defect), or auto-unwrap is genuinely missing (compiler gap). Not tagged without deciding which. |
| `app/devhub/adapter_bitbucket_curl_spec.spl` | 45/48 passed | Same `cannot index value of type enum` shape. Left RED with the row above. |
| `app/desugar/context_params_spec.spl` | 15/16 passed | Plain `expected false to equal true`; no missing symbol. Needs its own triage — not evidence of an unwritten feature. |
| `app/compile/cli_compile_surface_spec.spl` | **ABORT rc=124** | **Inconclusive, not a failure.** Hit the 900 s wall timeout. This is the spec that also hung an orphaned worker earlier, so the hang is reproducible and is worth its own bug record. |

**Running total across the whole slice: 248 specs executed, 54 not green, 0 tagged.**
Nine for nine, the failures were rename drift, import/visibility defects, a spec
bug, a concurrent lane's in-flight work, an ambiguous unwrap, or a hang. A
bulk-tag pass would have neutralised all nine and hidden every one of them.
That, rather than the coverage number, is this lane's actual result.


### Third harvest — 133 specs, 30 not green, still zero tagged

The sweep reached **133 specs: 103 green, 29 failing, 1 hung**. The failure rate
in this stratified sample is **22 %**, which is the single most useful number
this lane produced: it says the unit trees are far redder than the recorded DB
(Total 770 / Passed 0 / Failed 0) admits, and that whatever a full sweep costs,
it will surface on the order of **2,000 failing specs**, not a handful.

Additional failures triaged to a named cause:

| spec | cause | classification |
|---|---|---|
| `app/slang_pack/main_spec.spl` | `Cannot resolve module: app.svllm_pack.core` | **Half-finished rename.** `src/app/svllm_pack/` does not exist; the app now lives at `src/app/slang_pack/` (`core.spl`, 13 fns, including the `run` the spec imports). The source moved, the spec's `use` did not. |
| `app/svllm_pack/main_spec.spl` | identical import, identical failure | **Same rename, stale spec directory.** The whole `test/01_unit/app/svllm_pack/` tree is orphaned by that rename. Both specs carry the same `use app.svllm_pack.core.{run}` line 27. |
| `app/spec_to_spipe/census_spec.spl` | `variable run_widget not found` | No `fn run_widget` anywhere in `src/`. Symbol drift, not a declared-but-unbuilt feature. |
| `app/t32_cli/access_cli_grammar_spec.spl` | `expected 4 to equal 2`; `variable symbol not found` | Mixed assertion failure + symbol drift. Needs its own triage; no evidence of an unwritten feature. |

The remaining failures are listed in `/mnt/fast/tagsweep/final_results.tsv` with
their `Results:` lines. They are **left RED and untriaged** rather than tagged —
this lane ran out of box, not out of method, and an untriaged failure is exactly
what must not be tagged.

**Twelve failures triaged to a named symbol or line; zero were unfinished
features.** The dominant defect class by a wide margin is **rename/move drift**:
an implementation is renamed or relocated and its spec's `use` line is not
updated, so the spec fails at semantic analysis while the capability is present
and working. Seen here in `cli_passthrough` (`_append_cli_args_for_name` vs
`_cli_args_for_name`), `multi_mode_test_runner` (`execution_mode_from_string`
vs `parse_mode_str`), `dashboard_serve` (three `_run_*_result` helpers), and
`svllm_pack` -> `slang_pack` (two specs). That class is mechanically detectable
and would be a far better investment than tagging: a check that every `use
app.*` / `use std.*` target in a spec still resolves would have found five of
these without executing anything, in seconds rather than ~18 s per spec.


### Fourth harvest — all 30 failures now triaged, still zero tagged

Every one of the 29 failing specs plus the 1 hang has now been triaged to a
named symbol, line, or error class. **Zero are unfinished feature work, so the
final tag count for this slice is 0.** The classification, by class:

**A. Rename / move drift — the impl moved, the spec's `use` did not (5 specs).**
The single largest class. `svllm_pack` -> `slang_pack` (`src/app/svllm_pack/`
gone, code at `src/app/slang_pack/core.spl`; **two** specs still say
`use app.svllm_pack.core.{run}` at line 27), `_append_cli_args_for_name` vs the
live `_cli_args_for_name` (`src/app/mcp/cli_passthrough.spl:83`),
`execution_mode_from_string` vs `parse_mode_str` (`test_runner_args.spl:54`),
and three `_run_*_result` helpers that exist in
`src/app/dashboard/dashboard_export_runtime.spl` but are invisible to the spec.

**B. A spec correctly asserting a REAL PRODUCT BUG — must stay RED (1 spec).**
`app/ui_web/html_css_theme_authority_spec.spl` fails
`unknown variant or method 'default_spacing' on enum Spacing`. That is not the
spec's error: `default_spacing()` is defined on **`IOSSpacingScale`**
(`src/lib/common/ui/design_tokens.spl:199`), while `enum Spacing` is a different
type declared at `design_tokens.spl:3` — and
**`src/lib/nogc_sync_mut/ui/theme_package.spl:654` calls
`Spacing.default_spacing()`**, a method that type does not have. The spec is
right and the source is wrong. Per `.claude/rules/testing.md` this stays RED and
wants a `doc/08_tracking/bug/` record; tagging it would have hidden a live defect
in shipped stdlib UI code. **This one find justifies the whole classification
step.**

**C. Symbol / field / method absent, cause ambiguous — left RED per the
when-unsure rule (7 specs).** `run_widget` (no `fn run_widget` in `src/`);
`UiAccessNode has no field named 'text'` (the class exists and is widely used,
`src/lib/common/ui/access.spl`, so this is a wrong field name or a real gap —
undecided); `Module "app.test" does not export 'chrome_component_renderer_parity'`
(that name appears **nowhere** in `src/`, so the spec is either ahead of an
unwritten module or behind a deleted one — no evidence either way, so not
tagged); plus `unknown argument 'a'`, `variable 'symbol'`, `variable 'reason'`,
and `HOST`/`PORT`/`UNKNOWN_VAR` not found.

**D. Plain assertion failures needing individual triage (9 specs).**
`expected true, got false` and similar, with no missing symbol: the two
`ui.chromium.*` specs, `reftest_runner`, `checkpoint_spec` (also
`array index out of bounds: index is 0 but length is 0`), `context_params`,
`action_result`, `x25519mlkem768_browser_tls_fail_closed`, `census_spec`,
`offhost_assignment_todo_contract`. None shows evidence of an unwritten feature.

**E. Spec bug (1 spec).** `formatter_basic_spec.spl` interpolates `{clean_file}`
*inside* the expected string literal, so it resolves as a variable.

**F. Concurrent lane (1 spec).** `any_audit_classify_spec.spl` — another session
holds uncommitted edits to both the spec and `src/app/any_audit/classify.spl`.

**G. Hang (1 spec).** `app/compile/cli_compile_surface_spec.spl`, rc=124 at the
900 s wall. Reproducible: it also hung an orphaned worker earlier. Inconclusive,
not a failure, and worth its own bug record.

**Thirty for thirty, nothing qualified as `@tag:in-development`.** The tag means
"the feature is not written yet". In this sample the features were essentially
always written — what had rotted was the spec's reference to them, and in one
case what was broken was the shipped source. A bulk-tag pass over these trees
would have neutralised 30 red specs, hidden a real stdlib bug, and buried five
incomplete renames.


### Fifth harvest — 248 specs, 54 not green, still zero tagged

The sweep reached **248 specs: 194 green, 53 failing, 1 hung — a 21.8 % failure
rate**, statistically unchanged from the 22 % measured at 133 specs. The rate is
now stable across a sample nearly twice as large and spanning `app/`,
`browser/`, `browser_engine/`, `bugs/` and `compiler/`. **Extrapolated to the
9,458-spec work set that is roughly 2,000 failing specs** in the unit trees.

Coverage reached `compiler/` — the territory where an unfinished-feature tag was
most plausible. It did not change the answer. Twenty-three more failures were
triaged; **none qualified**, and the same two classes dominate.

**More rename / move drift (3 more, 8 total).** `compiler/ffi_gen/backend_gating_spec.spl`
fails `Cannot resolve module: compiler.tools.ffi_gen.main` — the module is
`sffi_gen`, not `ffi_gen` (`src/compiler/90.tools/sffi_gen/`), a one-letter
naming drift. `browser_engine/anonymous_block_spec.spl` fails
`function layout_context_new not found`, but that function exists **twice** —
`src/lib/gc_async_mut/gpu/browser_engine/layout_m14_types.spl:17` (`pub`) and
`src/lib/blink/layout/block_flow.spl:215`. Capability present, reference stale.

**A `bugs/` spec doing exactly its job — must stay RED.**
`test/01_unit/bugs/cast_else_swallows_outer_if_spec.spl` fails
`nil is forbidden by the non-optional return contract of '_naked_cast_else'`.
Its own docstring says it exists to "Prove that CastElse-swallows-outer-else
grammar pin" and it carries `# @req: REQ-BUGS-001`. The whole `test/01_unit/bugs/`
tree is, by construction, specs that document real defects. **Nothing under
`bugs/` is ever a candidate for this tag**, and a future sweep should exclude
that directory from tagging outright rather than re-deciding it per file.

**The most plausible tag candidate in the whole sweep, disproven (1).** Of 248
specs, the single best case for "the feature simply is not written yet" was
`compiler/mir_opt/auto_vectorize_spec.spl`, failing
`function LoopInfo not found` — an unimplemented MIR auto-vectorisation pass is
exactly the shape this tag exists for. It is implemented.
`src/compiler/60.mir_opt/mir_opt/auto_vectorize_analysis.spl` carries the
analysis (`is_simple_loop`, `detect_loop_bounds`, `analyze_loop_dependencies`),
with `_AutoVectorize/recipe.spl` and `_AutoVectorize/rewrite.spl` alongside it.
The type is named **`VectorLoopInfo`** (`auto_vectorize_types`), not `LoopInfo`.
Eighth instance of the same rename drift, and the one that settles the question:
even where an unwritten feature was most likely a priori, the feature was
present and the spec's reference was stale.

**Ambiguous, left RED (rest).** `method to_bytes not found on type str`
(`to_bytes` exists on several types but not `str` — possibly a real stdlib gap,
undecided); more `cannot index value of type enum`; and a long tail of plain
assertion mismatches (`expected 7 to equal 88`, `expected Any to equal
SiblingBox`, `expected true to equal false`, `expected 3 to equal 1`) that show
no evidence of an unwritten feature.

**Fifty-four for fifty-four, nothing qualified as `@tag:in-development`.** The
final tag count for this slice is **0**, and that is the finding, not a
shortfall: across 248 specs spanning five top-level areas, the unit trees'
redness is overwhelmingly stale references and real defects, not unbuilt
features.

## Left RED — with reasons (the honest state)

All nine failures found were classified and **none is unfinished feature work**,
so none was tagged. This is the whole point of the classification step: a
naive sweep would have tagged both and hidden two real defects.

### 1. `test/01_unit/multi_mode_test_runner_spec.spl` — 34 of 34 failed

**Spec rot against a renamed API. NOT in-development. Leave RED.**

Every example dies at semantic analysis with
`variable 'TestExecutionMode' not found` and
`function 'execution_mode_from_string' not found`. Two independent defects:

- `TestExecutionMode` **exists** — `src/lib/nogc_sync_mut/test_runner/test_runner_types.spl`,
  imported for real at `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl:25`.
  The spec's only import is `use std.spec` (line 18); it never imports the type
  it uses. That is a broken spec, not a missing feature.
- `execution_mode_from_string` **exists nowhere in `src/`**. The live spelling is
  `parse_mode_str` (`test_runner_args.spl:54`). The spec was written against a
  name that has since been renamed and was never updated.

A feature that is present and working cannot be "in development". Tagging this
would neutralise a spec that is simply wrong, and the rename would stay
undetected. Fix = add the import and rename the call; no feature work needed.

### 2. `test/01_unit/app/any_audit/any_audit_classify_spec.spl` — 1 of 22 failed

**Concurrent lane work in flight. NOT in-development. Leave RED.**

Fails `expected [field] to equal [generic]` — the classifier returns `field`
where the spec expects `generic`. Both sides of this pair are currently
**uncommitted, modified** in another session's working copy
(`src/app/any_audit/classify.spl` and this spec both appear as ` M` in that
tree's `git status`). Tagging a spec another lane is actively editing would
neutralise their red before they have finished; the tag would also have no
honest unblock condition, because the capability is being written right now.

## Mirror-tree note

No tags were applied, so no `test/unit/` twin needed one and
`scripts/check/check-test-tree-divergence.shs` is untouched by this lane.
Recorded for whoever continues: 4,484 of the 5,229 `test/unit/` specs are
byte-identical to their `test/01_unit/` twin, so a tag on any of those **must**
be applied to both files in the same commit or the divergence guard will fail.
The remaining 745 are twin-less or already divergent and can be tagged alone.

## What a follow-up lane should do differently

1. Do not attempt this slice serially on a contended box. 9,458 specs x ~18.5 s
   is ~48 hours; it needs a quiet box and real parallelism, or the mirror-twin
   saving plus a much longer window.
2. Keep the explicit-file-path invocation shape; a directory-shaped sweep needs
   `--no-cover-check --no-self-protect`, and even then must cross-check
   `Completed tests:` and short `Results:` counts.
3. Keep classifying. Two for two of the failures found here were *not*
   in-development, which is a strong prior that a bulk-tag pass over this tree
   would mostly mislabel real defects.

## Pre-existing test-tree divergence recorded at landing (mandatory)

`check-test-tree-divergence-delta.shs 673bfd5b9ca 21f73b1ad54` verdict:

```
base verdict: FAIL — 857 diverged vs 854 baselined (3 new, 0 fixed-but-still-baselined);
              1 mirror-only (0 unallowlisted, 0 stale-allowlist)
PASS — 3 pre-existing offender(s), 0 introduced by this range
```

Landing on a delta-PASS requires recording the pre-existing offender list, so it
is recorded here rather than stepped over silently. The three unbaselined
offenders, present at the base commit `673bfd5b9ca` and untouched by this range:

| offender | tree |
|---|---|
| `integration:storage/dbfs/dbfs_no_regression_spec.spl` | not this slice |
| `unit:os/kernel/arch/riscv32_boot_spec.spl` | **this slice** |
| `unit:os/kernel/loader/executable_source_vfs_spec.spl` | **this slice** |

Two of the three sit in this slice's own trees (`test/01_unit/` vs `test/unit/`).
They are **not** this lane's doing — this commit adds two documentation files and
changes zero files under `test/`, and the delta guard confirms 0 introduced — but
they are the kind of divergence a later tagging pass over these trees will trip
over, because a tag applied to one member of a diverged pair cannot be
mechanically mirrored. Whoever resumes this sweep should reconcile these two
pairs (or get them baselined deliberately) before tagging anything under
`os/kernel/`. Full 857-line list saved at
`/mnt/data/tmp/test_tree_divergence_preexisting.txt` (copy:
`/mnt/fast/tagsweep/preexisting.txt`).


## Full non-green list (248 specs executed)

```
test/01_unit/multi_mode_test_runner_spec.spl  ::  Results: 34 total, 0 passed, 34 failed
test/01_unit/app/compile/cli_compile_surface_spec.spl  ::  ABORT rc=124
test/01_unit/app/dashboard/dashboard_serve_spec.spl  ::  Results: 6 total, 0 passed, 6 failed
test/01_unit/app/desugar/context_params_spec.spl  ::  Results: 16 total, 15 passed, 1 failed
test/01_unit/app/devhub/adapter_bitbucket_curl_spec.spl  ::  Results: 48 total, 45 passed, 3 failed
test/01_unit/app/formatter/formatter_basic_spec.spl  ::  Results: 2 total, 1 passed, 1 failed
test/01_unit/app/mcp/cli_passthrough_spec.spl  ::  Results: 10 total, 3 passed, 7 failed
test/01_unit/app/mcp/assistant/session_store_spec.spl  ::  Results: 6 total, 0 passed, 6 failed
test/01_unit/app/provider_cli/native_provider_v1_spec.spl  ::  Results: 1 total, 0 passed, 1 failed
test/01_unit/app/release/install_font_assets_spec.spl  ::  Results: 2 total, 0 passed, 2 failed
test/01_unit/app/simple_lab/export_sdoctest_spec.spl  ::  Results: 9 total, 7 passed, 2 failed
test/01_unit/app/slang_pack/main_spec.spl  ::  Results: 1 total, 0 passed, 1 failed
test/01_unit/app/spec_to_spipe/census_spec.spl  ::  Results: 10 total, 9 passed, 1 failed
test/01_unit/app/svllm_pack/main_spec.spl  ::  Results: 1 total, 0 passed, 1 failed
test/01_unit/app/t32_cli/access_cli_grammar_spec.spl  ::  Results: 16 total, 13 passed, 3 failed
test/01_unit/app/test/chrome_component_renderer_parity/cache_spec.spl  ::  Results: 1 total, 0 passed, 1 failed
test/01_unit/app/test_runner_new/checkpoint_spec.spl  ::  Results: 8 total, 5 passed, 3 failed
test/01_unit/app/todo/offhost_assignment_todo_contract_spec.spl  ::  Results: 3 total, 2 passed, 1 failed
test/01_unit/app/tooling/algorithm_utils_spec.spl  ::  Results: 33 total, 28 passed, 5 failed
test/01_unit/app/ui/access_cli_spec.spl  ::  Results: 9 total, 8 passed, 1 failed
test/01_unit/app/ui.chromium.acid2/reftest_runner_spec.spl  ::  Results: 25 total, 24 passed, 1 failed
test/01_unit/app/ui.chromium.devtools/attach_session_spec.spl  ::  Results: 26 total, 20 passed, 6 failed
test/01_unit/app/ui_showcase/host_2d_vulkan_contract_spec.spl  ::  Results: 6 total, 5 passed, 1 failed
test/01_unit/app/ui.test_api/action_result_spec.spl  ::  Results: 1 total, 0 passed, 1 failed
test/01_unit/app/ui_web/html_css_theme_authority_spec.spl  ::  Results: 6 total, 1 passed, 5 failed
test/01_unit/app/ui/wire_golden/wire_golden_spec.spl  ::  Results: 4 total, 2 passed, 2 failed
test/01_unit/app/verify/release_bundle_loader_spec.spl  ::  Results: 1 total, 0 passed, 1 failed
test/01_unit/app/web/x25519mlkem768_browser_tls_fail_closed_spec.spl  ::  Results: 7 total, 6 passed, 1 failed
test/01_unit/app/web_packaging/advanced_packaging_spec.spl  ::  Results: 35 total, 32 passed, 3 failed
test/01_unit/browser_engine/anonymous_block_spec.spl  ::  Results: 4 total, 0 passed, 4 failed
test/01_unit/browser/script/canvas_api_spec.spl  ::  Results: 71 total, 70 passed, 1 failed
test/01_unit/bugs/cast_else_swallows_outer_if_spec.spl  ::  Results: 4 total, 3 passed, 1 failed
test/01_unit/compiler/bootstrap/ast_native_arena_spec.spl  ::  Results: 5 total, 1 passed, 4 failed
test/01_unit/compiler/codegen/any_typed_value_consumption_class_spec.spl  ::  Results: 5 total, 3 passed, 2 failed
test/01_unit/compiler/concurrent/concurrent_backend_store_parity_class_spec.spl  ::  Results: 1 total, 0 passed, 1 failed
test/01_unit/compiler/extern/rt_file_read_bytes_single_extern_signature_spec.spl  ::  Results: 7 total, 6 passed, 1 failed
test/01_unit/compiler/ffi_gen/backend_gating_spec.spl  ::  Results: 1 total, 0 passed, 1 failed
test/01_unit/compiler/hir/alias_static_call_resolution_spec.spl  ::  Results: 2 total, 0 passed, 2 failed
test/01_unit/compiler/interpreter/aliased_param_writeback_spec.spl  ::  Results: 4 total, 3 passed, 1 failed
test/01_unit/compiler/irdsl/parser_validator_spec.spl  ::  Results: 1 total, 0 passed, 1 failed
test/01_unit/compiler/linker/assurance_object_note_spec.spl  ::  Results: 5 total, 4 passed, 1 failed
test/01_unit/compiler/mir_opt/auto_vectorize_spec.spl  ::  Results: 64 total, 57 passed, 7 failed
test/01_unit/compiler/mir_opt/cipher/cipher_intrinsics_spec.spl  ::  Results: 30 total, 27 passed, 3 failed
test/01_unit/compiler/mono/verify/post_mono_verify_spec.spl  ::  Results: 9 total, 8 passed, 1 failed
test/01_unit/compiler/pipeline/cross_module_collision_detection_spec.spl  ::  Results: 2 total, 1 passed, 1 failed
test/01_unit/compiler/runtime/hosted_extern_mode_agreement_class_spec.spl  ::  Results: 1 total, 0 passed, 1 failed
test/01_unit/compiler/schema/generated_visitor_coverage_spec.spl  ::  Results: 11 total, 9 passed, 2 failed
test/01_unit/compiler/semantics/alloc_checker_spec.spl  ::  Results: 28 total, 27 passed, 1 failed
test/01_unit/compiler/tools/verify/allocator_symbol_scan_spec.spl  ::  Results: 13 total, 12 passed, 1 failed
test/01_unit/compiler/traits/conformance/trait_conformance_enforced_class_spec.spl  ::  Results: 5 total, 3 passed, 2 failed
test/01_unit/compiler/type_infer/method_call_inference_spec.spl  ::  Results: 4 total, 2 passed, 2 failed
test/01_unit/compiler/types/declared_return_type_enforced_spec.spl  ::  Results: 3 total, 1 passed, 2 failed
test/01_unit/coupling/coupling_metrics_spec.spl  ::  Results: 109 total, 104 passed, 5 failed
test/01_unit/doc/de10nano_quartus_setup_spec.spl  ::  Results: 1 total, 0 passed, 1 failed
test/01_unit/examples/graphics_2d_showcase_wm_client_events_spec.spl  ::  Results: 3 total, 2 passed, 1 failed
test/01_unit/hal/hal_traits_spec.spl  ::  Results: 30 total, 26 passed, 4 failed
test/01_unit/hardware/riscv_common/riscv_formal_contract_spec.spl  ::  Results: 1 total, 0 passed, 1 failed
test/01_unit/hardware/rv32i/rv32_sv32_walker_spec.spl  ::  Results: 1 total, 0 passed, 1 failed
test/01_unit/hardware/rv32imac/rv32_alu_spec.spl  ::  Results: 1 total, 0 passed, 1 failed
```
