# scv structural 3-way merge falls back to conflict-data and drops one side's edit

Date: 2026-08-27
Status: BLOCKED (triage 2026-11-11, lane boot22) — executed re-verification
forbidden in-lane: the finding spec requires the deployed self-hosted binary
`bin/release/simple`, absent here, and the tracked seed cannot run the scv CLI
at all (`unknown extern function: rt_file_modified_time` — seed/source drift,
redeploy belongs to the seed-fix lane). Verbatim grant in the 2026-11-11
addendum below. The 2026-08-27 "owned by another in-flight session" note is
stale: this branch's merge path landed wholesale via PR #7597 (2026-11-07).
Class: (b) real product bug
Found by: root-causing long-standing RED `test/integration/app/scv_structural_match_spec.spl` (5/8)

## Ownership / hands-off note
The structural-merge implementation (`merge.spl`, `region_merge.spl`,
`merge_validation.spl`, `conflict_v2.spl` and the merge corpus) is currently
owned by another in-flight session working the open defect
`scv_merge_silently_merges_across_divergent_preprocessor_branches_2026-08-26.md`.
This record deliberately does NOT change any of those files. It exists because
that record does not mention these three examples, and the failures here are a
different observable shape (conflict + data loss, not a silent wrong merge), so
they would otherwise stay unrecorded.

## Symptom
Three examples fail, all in the structural-merge path. In every one, `merge`
reports `conflicts=1` with the per-file strategy `conflict-data`, where the spec
requires a clean structural merge — and the merged content **silently drops one
side's edit** rather than preserving both.

1. "structural 3-way merge applies disjoint named-anchor edits without conflict"
   -> `code.spl: conflict-data`, `conflicts=1`.

2. "structural merge preserves moved function body from left and right edit
   without conflict"
   -> `code.spl: conflict-data`, `conflicts=1`,
      `merged=fn gamma():|    pass|fn alpha():|    base_body|`
      The spec requires `right_body`; the merge kept `base_body`, i.e. the right
      side's edit was discarded.

3. "gracefully degrades to line merge and logs fallback strategy for kind-line
   files"
   -> `broken.spl: conflict-data`, `conflicts=1`,
      `merged=ONE|two|three|` where the spec requires `merged=ONE|two|THREE|`.
      The left edit (`ONE`) survived; the right edit (`THREE`) was lost.

## Why this matters
The strategy label `conflict-data` suggests the merge recognised a conflict, but
the emitted merged content is not a conflict region — it is one side silently
chosen over the other. That is data loss, not a surfaced conflict, and it is
worse than a reported conflict because the user is not prompted to resolve it.
Example 3 is the clearest: the fixture is designed so line-merge fallback should
combine two disjoint single-line edits, which line merge handles trivially.

## Evidence
Baseline run (unmodified tree at f2e10076977):
`Results: 8 total, 5 passed, 3 failed`. Verbatim actual-vs-expected for all
three examples is quoted above, taken from the spec run log.

## Classification note
These are NOT stale specs and NOT environment. The specs assert behaviour the
feature is documented to provide (structural anchor matching, and line-merge
fallback for kind-line files); the product returns a conflict and loses an edit.
No spec change is appropriate here — the fix belongs in the merge path.


## 2026-11-11 P3-boot22 triage — BLOCKED (header flip, grant recorded)

Row 5 of lane boot22 (bootstrap table, after #40). What was re-verified FRESH
at this lane's base (`79d5af6723f6`, tracked seed build `46fe8f6b6def`):

- **Spec cannot execute in-lane.** Every one of the 8 cases in
  `test/02_integration/app/scv_structural_match_spec.spl` shells out to
  `$REPO/bin/release/simple` (hardcoded path, e.g. spec :41); this worktree has
  only the tracked seed `bin/simple.exe`, so all 8 fail with
  `/usr/bin/sh: ... bin/release/simple: No such file or directory`. That 8/8
  shape is environmental, NOT this defect — do not cite it as a repro either
  way.
- **The tracked seed cannot run the scv CLI at all.** Hand-driven equivalent
  of the spec's scripts dies at the first `snapshot` with
  `error: semantic: in call to scv_cli_result ... unknown extern function:
  rt_file_modified_time`. The extern EXISTS in tree source
  (`src/runtime/runtime_core_io_exports.c:46-51`) — the tracked seed binary
  predates it (seed/source drift; tracked-seed redeploy belongs to the
  seed-fix lane).
- **The 2026-08-27 ownership note is stale on this branch.** `merge.spl`,
  `merge_validation.spl`, and `conflict_v2.spl` did not exist at the first
  parent of PR #7597 (`9e7e7a526edb`, 2026-11-07); this branch's entire merge
  path (+885 lines) arrived with that merge. Whether the recorded
  conflict-data/data-loss examples still reproduce in that implementation is
  UNKNOWN — execution is the only honest answer and it is blocked above.

Verdict: BLOCKED — not LIVE-by-default (the source under test changed
wholesale after the recording) and not SUPERSEDED (no evidence the three
examples pass).

Verbatim grant: on a host with the deployed self-hosted binary, run
`SIMPLE_LIB=src bin/release/simple test test/02_integration/app/scv_structural_match_spec.spl --no-cache`
(or equivalently with `bin/release/<triple>/simple` on PATH as
`bin/release/simple`) and record the per-case verdicts. The three cases named
in this record are "gracefully degrades to line merge and logs fallback
strategy for kind-line files", "structural 3-way merge applies disjoint
named-anchor edits without conflict", and "structural merge preserves moved
function body from left and right edit without conflict". Ownership question
from 2026-08-27 (who may edit `merge*.spl`/`conflict_v2.spl`) must be
re-resolved against the PR #7597 merge-path owner before any fix lands.
