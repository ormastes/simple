# Push runtime-API guard rescans identical base and tip surfaces

**Date:** 2026-08-24
**Status:** RESOLVED
**Owner:** must-check push-tier lane

## Problem

`check-runtime-api-regression-push.shs --scan-only` extracted every Rust and C
runtime definition from both endpoints even when Git proved neither runtime
tree changed. On a docs/check-only committed range this took 7.43 seconds and
10,496 KiB peak RSS, consuming most of the ten-second push budget.

## Resolution

The evaluator first asks Git whether either
`src/compiler_rust/runtime/src` or `src/runtime` differs. An unchanged surface
is identical by committed tree content, so it extracts the tip once and still
requires a positive real symbol count. A changed surface retains the complete
base/tip definition, re-export, removal, and unbuildable-tree analysis. Git
comparison failure remains ERROR.

The first tree-equality change reduced the same committed-range scan from 7.43
seconds/10,496 KiB to 3.89 seconds/10,240 KiB. Profiling then showed each
remaining extraction still spawned one `git show` per runtime file. Two
committed-tree `git grep` operations now extract the complete Rust and C sets.
Their outputs were compared before replacement: Rust 1,804 versus 1,804 and C
1,504 versus 1,504, byte-for-byte identical in both cases.

The final scan takes 0.84 seconds and 35,328 KiB peak RSS: 88.7% lower latency
than the 7.43-second baseline. All four mutation fixtures pass, including
incident replay, forward progress, intentional single removal, and the
unchanged-range non-vacuity case.
