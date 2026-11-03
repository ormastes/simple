# no-stale-snapshot-rewind gate missed PR #6132's rewind (threshold 5, advisory at push)

Status: fix implemented and verified; landing pending (P2). Filed 2026-11-03.

## Incident
PR #6132 (`work/owner-transport-av`, single commit `8382092ddf4`, parent `eb686ac15dc` =
merge of PR #6130) rewound three #6130 frontend files; PR #6136 restored them.
Earlier rewinds: #6093 (fixed by #6094), #6109 (fixed by #6117).

## Repro (read-only, committed content; takes ~2 min on Windows)
```
git fetch origin
sh scripts/check/check-no-stale-snapshot-rewind.shs --range eb686ac15dc..8382092ddf4
```
Output (verdict is PASS):
```
window: 40 ancestor(s)  threshold: 5 file(s)  min-lost: 4 line(s) / 25%
  8382092ddf4: 2 rewound file(s)
    parents=1 scoped-changed=5 scored=3 window=40
    src/compiler/10.frontend/core/_ParserDecls/fn_struct_decls.spl - drops 15 of 23 live line(s) landed by eb686ac15dc
    src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl - drops 13 of 14 live line(s) landed by eb686ac15dc
PASS - 1 commit(s) checked, 0 rewind(s)
```
Running against the merge commit `2d7271296c1` is moot: it is a 2-parent merge (the gate scores
single-parent commits), so only the PR's own commit range can catch it.

## Root causes (in order of weight)
1. **Threshold, not detection.** The gate DID find the rewind (2 of 3 files; `module_assembly.spl`
   fell under the 4-line/25% floor) but `THRESHOLD=5` files is needed to FAIL
   (`check-no-stale-snapshot-rewind.shs:167`). A small PR-sized stale snapshot (3-4 files, all
   from ONE just-landed contributor) is below the snapshot-sized budget. Window (40 first-parent
   ancestors) and merge handling are NOT the cause: the contributor `eb686ac15dc` is the parent
   itself and is scored via `X^1..X`.
2. **Not enforced at push.** `push-no-stale-snapshot-rewind` is `push_blocking=false`
   (`config/check/must_check_gates.sdn:56`, demoted 2026-09-24 for cost: 47-128 s) and advisory
   rows are skipped on ordinary pushes; it only remains in CI `fast-gates`, same threshold.
3. **Admin merges** skip the strict re-run, so the CI verdict (also PASS here) is the only net.

## Repair (2026-11-03)
The gate retains its historical five-file threshold and additionally rejects
two or more files each losing at least 50% of the direct parent's live added
lines. Existing four-line absolute floor, scoped paths, bulk-contributor
exclusion, declared-revert file exclusions and `Rewind-Allowed` counts apply.
The parent is processed first, so per-file attribution cannot be displaced by
an older contributor. This deliberately protects the direct parent only;
small rewinds of older contributors remain below the historical threshold.

Embedded Git fixtures cover a two-file total rewind, a focused one-file edit,
substantive two-file edits losing 40%, the exact 50% boundary, a two-file
declared revert, and an explicit two-file allowance. The existing broad-loss,
rename, line-ending and cache-failure fixtures are preserved.

This repair does not promote the advisory push gate or claim a startup-time
improvement. A parent-only recent-commit sample evaluates the new rule, not
the complete 40-ancestor historical profile.

### Retained verification evidence

- Historical incident baseline, `--window 1 --range eb686ac15dc..8382092ddf4`:
  wrongly PASSed despite reporting two parent-loss files (15/23 and 13/14).
- Ten most recent single-parent commits reachable from `1b07d73a10e`, excluding
  the historical incident: all PASS with `--window 1`; 17–31 seconds each on
  this Windows host. This is a bounded false-positive sample of the new rule,
  not proof that the full gate is faster or all legitimate edits are accepted.
- `bash -n`, `git diff --check`, both direct-env runtime guard modes: PASS.
  `doc/06_spec/**/*_spec.spl`: zero files.
- Before-fix selftest: 14 fixtures, exactly one failure, the new two-file
  parent-rewind control. After-fix selftest: 14 fixtures, zero failures; all
  four exact/removed/lone-CR/binary line-ending criteria PASS. The subsequent
  historical incident run correctly rejects both files with a final FAIL.
- Six focused parent controls: zero failures, including substantive 40% edits,
  exact 50% loss, one-file replacement, total two-file loss, an allowance and
  a declared revert. These controls ran with a 40-ancestor window; embedded
  fixtures use a parent-only window to avoid rescoring irrelevant older
  fixture history. No broader false-positive or push-enforcement claim.
- Private diagnostic logs: `C:/dev/wt/p2-rewind-baseline.log`,
  `p2-rewind-census.log`, `p2-rewind-controls-before.log`,
  `p2-rewind-fixed-selftest.log`, and `p2-rewind-new-controls.log` in the same
  directory. All campaigns completed before the 07:30 UTC deadline; no retry.

## Original proposal
Add a concentration rule: FAIL when >= 2 files each lose >= 50% of the live lines of the SAME
contributor that is the commit's direct parent (or a merge landed within the last N commits) and
the commit is not a revert (`This reverts commit`) and carries no `Rewind-Allowed:`. Needs
selftest fixtures (2-file rewind of parent contribution must FAIL; ordinary edit of own file
must PASS) and a false-positive census over recent main. Also consider a fast-path (<20 s) for the
parent-only contributor so it can return to the push tier.
