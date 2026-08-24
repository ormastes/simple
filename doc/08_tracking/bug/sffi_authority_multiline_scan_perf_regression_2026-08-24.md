# Multiline SFFI authority scan performance is not yet accepted

**Status:** Open

## Evidence

On the same source revision, the committed scanner completed the `--summary`
command in 40.85 seconds with 14,132 KiB peak RSS. The multiline-aware scanner
reported 43.81 seconds / 14,632 KiB, then 57.09 seconds / 14,504 KiB after a
one-line-header fast path. The functional totals were stable across corrected
runs: 21,556 calls, 2,187 explicit, and 19,369 missing.

The host timing is noisy, but no corrected run proves the scanner stays within
the prior wall-time envelope. The hard three-cycle cap prevents further retry
in this session. Do not claim a performance pass from the unchanged linear
complexity alone.

## Required repair

Profile signature discovery separately from the existing masking and report
generation. Replace repeated per-header lookahead with one line-indexed
signature-end pass if it is the measured bottleneck. Preserve O(source bytes +
call sites), exact line numbers, prose masking, and the multiline selftest.

## Acceptance

Run the identical same-tree `--summary` command before and after under an idle
host. The corrected scanner must remain within 5% wall time and 1 MiB peak RSS,
while retaining the 289 newly discovered call rows.
