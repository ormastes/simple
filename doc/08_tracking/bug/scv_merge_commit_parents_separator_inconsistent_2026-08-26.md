# SCV: merge-commit `parents:` separator inconsistent across readers (2026-08-26)

**Status:** OPEN (partial). `merge.spl` now writes `parents: <left> <right>` (space-joined).

## What was wrong
`scv_merge_commits` wrote `parents: <left>,<right>` (comma). `scv_write_operation`
(`store.spl`) validates every parent by splitting on `" "`, so the comma-joined token never resolved
to a commit object and **every `merge-commits` call failed with `ERROR invalid operation commit parent`**
(`scv_merge_spec` red). Fixed by space-joining, which is what `scv_commit_parents`, `working_copy.spl`,
`fast_import.spl`, `native_shadow.spl`, `integrity_commit.spl` and the store validator already expect.

## Still inconsistent (not owned by wave-3 lane D)
These readers still split `parents` on `","` and will misparse a space-joined merge commit as one
parent token: `integrity_view.spl:132`, `recover.spl:76`, `maintenance.spl:283`, `integrity.spl:418`.
They need to split on `" "` (and tolerate `","` for any legacy objects). No spec pins them yet.
