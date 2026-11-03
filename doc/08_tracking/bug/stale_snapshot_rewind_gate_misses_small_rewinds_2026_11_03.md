# no-stale-snapshot-rewind gate missed PR #6132's rewind (threshold 5, advisory at push)

Status: open (P2). Filed 2026-11-03.

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

## Proposed fix (not done here)
Add a concentration rule: FAIL when >= 2 files each lose >= 50% of the live lines of the SAME
contributor that is the commit's direct parent (or a merge landed within the last N commits) and
the commit is not a revert (`This reverts commit`) and carries no `Rewind-Allowed:`. Needs
selftest fixtures (2-file rewind of parent contribution must FAIL; ordinary edit of own file
must PASS) and a false-positive census over recent main. Also consider a fast-path (<20 s) for the
parent-only contributor so it can return to the push tier.
