# Push must-check ten-second NFR

**Date:** 2026-08-24
**Status:** RESOLVED — linear ledger parsing restored margin below ten seconds
**Owner:** must-check push-tier lane

## Current evidence

The exact committed-ref production consumer passes functionally but measures
11.05 seconds and 225,736 KiB peak RSS, exceeding NFR-MCT-001 by 1.05 seconds.
This is the third whole-path optimize/fix cycle, so no further tuning was
started in this session.

On 2026-08-24 a fresh session replaced the per-field/per-row shell parsing in
`validate_ledger_text` with one linear `awk` cross-check plus evidence hashing
only for PASS rows. The same committed-ref command measured 6.10 seconds and
224,968 KiB immediately before the change, then 4.84 seconds and 224,840 KiB
after it: 1.26 seconds (20.7%) faster with effectively unchanged peak RSS. The
focused 20-fixture ledger self-test passed after the change, including explicit
rejection of a failed nonblocking row.

The latest component profile before the final runtime batching measured:

| component | elapsed |
|---|---:|
| tree-size committed-tip guard | 1.78s |
| quick rules committed-ref guard | 2.65s |
| interpreter module owners | 0.69s |
| runtime API scan | 3.70s before batching; 0.84s after |
| conflict tree + markers + interpreter extern + type walk | 0.99s combined |

The original path had roughly four seconds of ledger parsing, fingerprinting,
dispatch, and other wrapper overhead in addition to the retained gates. The
linear parser removes the dominant repeated-process component without moving
any load-bearing conflict, structural, or runtime-deletion check.
