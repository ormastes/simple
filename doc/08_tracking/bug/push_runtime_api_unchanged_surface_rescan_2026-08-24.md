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

The same committed-range scan now takes 3.89 seconds and 10,240 KiB peak RSS
(47.6% lower latency). All four mutation fixtures pass, including incident
replay, forward progress, intentional single removal, and the unchanged-range
non-vacuity case.
