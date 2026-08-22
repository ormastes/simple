# Pre-push tree guard repeats full-tree scans per commit and ref

Status: OPEN — performance follow-up

## Evidence

`check-push-must-pass.shs` invokes the outgoing-history guards once for every
pushed ref. `check-tree-size-push.shs` materializes the complete revision list
in a shell variable, then performs multiple recursive tree listings plus a sort
for every commit. Overlapping ref ranges and identical tree objects are not
deduplicated. Complexity is approximately `O(refs * commits * entries log
entries)` with `O(commits)` shell memory. The existing retained bug evidence in
`pre_push_guards_exit_silently_with_no_verdict_2026-08-10.md` measures the tree
guard self-test at about four minutes, consistent with the script's own warning
that thousands of Git processes can exceed 600 seconds.

## Required fix

Preserve guard results and hook ordering while streaming the union of outgoing
commits, inspecting each unique tree object once, and bounding history/evidence
work with explicit diagnostics. Compare the same multi-commit/multi-ref fixture
before and after, including elapsed time and peak RSS. This broader guard
algorithm change is intentionally separate from the narrow bootstrap identity
contract repair.
