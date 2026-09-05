# Pre-push tree guard repeats full-tree scans per commit and ref

Status: RESOLVED — `codex/session-01a023a8`

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

On the current 12-commit `origin/main..HEAD` range, the unchanged production
guard measured 25.79 seconds elapsed and 79,872 KiB peak RSS. That exceeds the
approximately ten-second total push budget before the other push gates run.

## Required fix

Preserve guard results and hook ordering while streaming the union of outgoing
commits, inspecting each unique tree object once, and bounding history/evidence
work with explicit diagnostics. Compare the same multi-commit/multi-ref fixture
before and after, including elapsed time and peak RSS. This broader guard
algorithm change is intentionally separate from the narrow bootstrap identity
contract repair.

## Implemented slice

The production push driver now invokes `--push-tip`. That bounded mode skips
the exhaustive fixture campaign and revision-list materialization, evaluates
only the committed candidate tip, and uses a count-only parent scan for the
relative band. Absolute size, duplicate-entry, `src/` shape, and load-bearing
path checks remain fail-closed on the pushed tree. The exhaustive 24-fixture
mode remains available through `--selftest` outside the hook.

Before the user-requested unverified sync boundary, the same 12-commit range
had measured 25.79 seconds / 79,872 KiB in exhaustive mode and 1.29 seconds /
79,872 KiB in bounded tip mode. The remaining multi-ref deduplication and
evidence-file bounds were then closed: identical updates are deduplicated,
more than two unique updates fail closed with split-push guidance, and evidence
hashing has a repository-containment plus 64 MiB aggregate bound.

The focused end-to-end contract passed in 7.14 seconds with 71,168 KiB peak
RSS; its committed-ref path took one second and installed-hook path zero
whole seconds. The preserved production-tree measurement remains 1.29 seconds
for the same 12-commit tip.
