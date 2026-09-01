# scv structural 3-way merge falls back to conflict-data and drops one side's edit

Date: 2026-08-27
Status: OPEN — NOT FIXED HERE (merge path is owned by another agent; see "Ownership")
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
