# Admission rejected de-symlink PRs: type_changed unsupported (2026-09-18)

## Symptom

PR #1111 (beta.13: replace 11 symlinked .spl files under `src/` with real
copies to unblock the SCV freeze on the windows release leg) passed the
ratchet but the required `SPipe Self Review Admission` check rejected it
**6 consecutive times** (~30 s per dispatch) with:

> Rejection reason: changed-path status is unsupported: type_changed

## Root cause

- The changed-path manifest generator
  (`scripts/release/self-review-changed-manifest.shs`) maps git status `T`
  to `status: type_changed` (mode 120000 -> 100644) and has always emitted it.
- The policy evaluator (`scripts/release/self-review-policy-evaluator.mjs`,
  `changeShapeError`) had shape rules for `added`, `modified`/`mode_changed`,
  `deleted`, `renamed`/`copied` — and nothing else, failing closed with
  "changed-path status is unsupported".

Any PR that converts a symlink to a regular file (exactly what the SCV
freeze gate demands on this repo, since the SCV snapshot reader is no-follow
by design, `src/lib/scv/compile_snapshot.spl:109`) could therefore **never**
pass self-review admission. Not beta-specific — a structural policy gap.

## Fix

PR #1118: admit `type_changed` with exactly one shape —
`previous_file_type: symlink` -> `file_type: regular`, utf8 on both sides,
no `previous_path`. The reverse direction (regular -> symlink, i.e.
introducing new symlinks) and non-utf8 shapes stay closed.

Unit tests in `test/01_unit/app/release/self_review_policy_evaluator_test.mjs`
cover the admitted shape plus two rejected shapes; the real 32-path PR #1111
manifest was replayed against the fixed evaluator to confirm the rejection
is gone.

## Evidence

- Rejection: check-run 105765267173 (dispatch run 35396004445), output
  "changed-path status is unsupported: type_changed".
- Local replay: `parseChangedManifest` on the generated PR #1111 manifest
  → valid, 32 changes; `evaluateSelfReview` no longer reports the
  type_changed rejection.
