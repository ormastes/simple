# C1 assessment — `src/lib/common/` closure (engine2d + render_opt) — 2026-08-07

Plan: `doc/03_plan/ui/testing/render_2d_vulkan_functional_coverage_plan_2026-08-07.md`
(Unit C1, lines 432-441). Session context: coverage EXPORT landed (`ae97a34cd365`)
and flipped gate prerequisite 4 (artifact export) to MET; this unit assesses
whether C1 is now achievable on top of that.

## Verdict: C1 as written is NOT achievable. Delivered instead: a labeled, artifact-verified LINE-coverage-only partial.

Two independent blockers, both re-verified this session, not assumed from the bug doc:

1. **Acceptance command's own first two lines fail.** C1's acceptance command
   (plan line 435-437) is:
   ```
   bin/simple spl-coverage clear
   SIMPLE_COVERAGE=1 bin/simple test test/01_unit/lib/common/ --no-cache --no-cover-check
   bin/simple spl-coverage dump | <B1 report filter> ...
   ```
   `bin/simple spl-coverage status` → `file not found: spl-coverage`. Gate
   script `scripts/check/check-render2d-coverage.shs` confirms:
   `prereq3_spl_coverage_dispatchable` is **UNMET**. There is no `spl-coverage`
   subcommand and no `<B1 report filter>` to pipe into.
2. **No branch/arm data exists at all, in any artifact.** C1's body (line
   439-441) asks to "close remaining arms... typically clip degenerate
   branches, seal/reject arms, empty-input early returns," naming its
   `it "covers <fn> <condition> arm"`. I measured six real
   `SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<path> bin/simple test <spec> --coverage`
   runs against every spec covering the two target module trees and inspected
   every artifact's section headers:
   ```
   $ grep -n '^[a-z_]* |' <artifact>.sdn   # only ever: "lines |...|" and "functions |...|"
   $ grep -ic branch /tmp/c1cov/*.sdn      # 0 for all six artifacts
   ```
   There is no branch inventory to name arms from. "Close remaining arms" has
   no primitive to close against.

Both blockers independently kill C1's literal acceptance criteria — the CLI
gap (1) is the cheaper one to re-verify by hand.

## What was executed instead (LINE coverage, real artifacts, explicitly partial)

Ran all six specs that `@cover`-annotate or import the two C1 module trees,
each with a fresh `SIMPLE_COVERAGE_OUTPUT` artifact path:

| spec | Results: line | artifact bytes |
|---|---|---|
| `test/01_unit/lib/common/gpu/engine2d/scalar_oracle_spec.spl` | `Results: 44 total, 44 passed, 0 failed` | 15688 |
| `test/01_unit/lib/common/gpu/engine2d/kernel_registry_spec.spl` | `Results: 10 total, 10 passed, 0 failed` | 7647 |
| `test/01_unit/lib/common/ui/render_opt/draw_ir_delta_spec.spl` | `Results: 6 total, 6 passed, 0 failed` | 5705 |
| `test/01_unit/lib/common/ui/render_opt/paint_chunk_rasterizer_spec.spl` | `Results: 6 total, 6 passed, 0 failed` | 10492 |
| `test/01_unit/lib/common/ui/render_opt/render_opt_invalidation_spec.spl` | `Results: 18 total, 18 passed, 0 failed` | 14186 |
| `test/01_unit/lib/common/ui/render_opt/property_trees_revisions_spec.spl` | `Results: 10 total, 10 passed, 0 failed` | 8651 (needed `--no-session-daemon --sequential`; timed out at 120s under the daemon — operational finding, not a defect in the coverage path) |

All six green, all six artifacts non-empty and containing real per-line
`file, line, hit_count` records with real absolute paths and real line numbers
(not `"<source>"`, not `0,0`).

### Per-file LINE percentages — sourced ONLY from the tool's own stdout banner, never from a hand-rolled line-count proxy

Each row below is a single self-consistent run: numerator, denominator, and
percentage all printed by the coverage tool itself in that run's stdout, then
cross-checked against that run's own artifact (`hit_count>0` entry count for
the file matches the banner's numerator exactly in all 9 cases):

```
coverage: src/lib/common/gpu/engine2d/kernel_registry.spl 65% (62/95 lines)   [from kernel_registry_spec]
coverage: src/lib/common/gpu/engine2d/kernel_registry.spl 67% (64/95 lines)   [from scalar_oracle_spec]
coverage: src/lib/common/gpu/engine2d/scalar_oracle.spl 89% (95/106 lines)    [from scalar_oracle_spec]
coverage: src/lib/common/ui/render_opt/draw_ir_delta.spl 100% (16/16 lines)   [from draw_ir_delta_spec]
coverage: src/lib/common/ui/render_opt/paint_chunk_rasterizer.spl 95% (39/41 lines) [from paint_chunk_rasterizer_spec]
coverage: src/lib/common/ui/render_opt/property_trees.spl 51% (66/128 lines)  [from property_trees_revisions_spec]
coverage: src/lib/common/ui/render_opt/property_trees.spl 85% (109/128 lines) [from render_opt_invalidation_spec]
coverage: src/lib/common/ui/render_opt/revisions.spl 36% (22/61 lines)        [from property_trees_revisions_spec]
coverage: src/lib/common/ui/render_opt/revisions.spl 65% (40/61 lines)        [from render_opt_invalidation_spec]
```

**Denominator caveat (why no single aggregate is claimed for the whole
module tree):** the banner is only printed for files a given spec `@cover`-
annotates. The artifact's `lines` section also records hit entries for files
a spec touches incidentally through imports (e.g. `draw_ir_delta_spec`'s
artifact has 28 hit-lines for `revisions.spl` with no banner in that run) —
those incidental hits have no tool-confirmed denominator in that run, so they
are **excluded** from the table below rather than assumed consistent with the
denominator seen in a different run.

**Best-per-file, using only banner-confirmed rows** (max hit count, same
denominator both times it was independently reported — 95, 128, 61 agreed
across their two runs each, which is reassuring but only two data points):

| file | best hit/total | pct |
|---|---|---|
| `scalar_oracle.spl` | 95/106 | 89.6% |
| `kernel_registry.spl` | 64/95 | 67.4% |
| `draw_ir_delta.spl` | 16/16 | 100.0% |
| `paint_chunk_rasterizer.spl` | 39/41 | 95.1% |
| `revisions.spl` | 40/61 | 65.6% |
| `property_trees.spl` | 109/128 | 85.2% |
| **sum** | **363/447** | **81.2%** |

This 81.2% is **LINE coverage only**, over 6 of the module trees' files (not
an exhaustive file list for the two C1 target directories — only the files
these six existing specs `@cover`), and is **not** a substitute for the
branch/arm closure C1 asks for.

## Explicit non-claims

- No branch-coverage percentage is reported anywhere in this document, for
  any file, under any framing.
- No new spec was written and no `it` was added. Adding its to move the line
  numbers above would not verifiably "close an arm" per C1's own naming
  convention (`it "covers <fn> <condition> arm"`) without arm/branch identity,
  which does not exist — that would be exactly the fabrication risk this
  session's `CLAUDE.md` and bug-tracking rules warn against.
- **Sabotage-verification does not apply**: the standing convention requires
  sabotage-testing *new* specs; none were written. This document measures six
  pre-existing, already-passing specs.
- The gate script (`scripts/check/check-render2d-coverage.shs`) was not
  edited. B1's fail-closed design (it must never go green while the
  underlying artifact is fabricated or absent) is respected as-is.

## Discrepancy note (plan/bug-doc assumption re-checked, per repo convention)

The bug doc's prerequisite 1 claims the decision-probe call sites hardcode
`"<source>"` / `0,0` identity. That claim is about the **branch/decision**
probe path specifically. The **line**-export path measured here shows real
absolute file paths and real line numbers in every one of the six artifacts
— e.g. `/home/ormastes/dev/pub/simple/src/lib/common/gpu/engine2d/kernel_registry.spl, 79, 1`.
This does not flip prereq1 to MET (prereq1 is scoped to the decision-probe
sites, which remain unverified here and there is still no `branches` section
anywhere), but it is worth recording: the line-identity half of the pipeline
is demonstrably real, and prereq1's premise deserves separate re-verification
for the branch-probe half specifically, not blanket citation against both.

## Gate re-run (same script, unedited)

```
$ sh scripts/check/check-render2d-coverage.shs
[UNMET] prereq3_spl_coverage_dispatchable -- bin/simple spl-coverage status -> 'file not found: spl-coverage'
[MET]   prereq4_artifact_export -- artifact written and non-empty
[UNMET] prereq1_real_source_spans_UNVERIFIED_BY_SCRIPT
[UNMET] prereq2_production_mir_coverage_lowering_UNVERIFIED_BY_SCRIPT
[UNMET] prereq5_perfile_rollup_UNVERIFIED_BY_SCRIPT
FAIL — 5 prerequisite(s) checked, 4 unmet (do not report a branch-coverage percentage)
```

Unchanged from before this session's C1 work: 1 MET (prereq4), 4 UNMET
(prereq1, prereq2, prereq3, prereq5). **C1/C2/C3 stay blocked** on branch
coverage per B1's own gate. This session did not, and could not, move that
gate — only the line-coverage side had anything left to measure.

## Disk

Before: 238G free on `/`. After: 238G free on `/` (report-doc write only, no
build/bootstrap run). Both well above the 100G floor.

## Binary provenance

`readlink -f bin/simple` → `/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple`
(Rust seed lane, per `.claude/rules/bootstrap.md` naming — this is the shared
deployed binary, unmodified by this session).
