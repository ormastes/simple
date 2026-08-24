# Push must-check remains above the strict ten-second NFR

**Date:** 2026-08-24
**Status:** OPEN — three-cycle optimization cap reached
**Owner:** must-check push-tier lane

## Current evidence

The exact committed-ref production consumer passes functionally but measures
11.05 seconds and 225,736 KiB peak RSS, exceeding NFR-MCT-001 by 1.05 seconds.
This is the third whole-path optimize/fix cycle, so no further tuning was
started in this session.

The latest component profile before the final runtime batching measured:

| component | elapsed |
|---|---:|
| tree-size committed-tip guard | 1.78s |
| quick rules committed-ref guard | 2.65s |
| interpreter module owners | 0.69s |
| runtime API scan | 3.70s before batching; 0.84s after |
| conflict tree + markers + interpreter extern + type walk | 0.99s combined |

The final whole path therefore has roughly four seconds of ledger parsing,
fingerprinting, dispatch, and other unprofiled wrapper overhead in addition to
the retained gates. The next session should profile those owners once, starting
with repeated SDN parsing/fingerprinting and the rules/tree-size scans. Do not
move the remaining load-bearing conflict, structural, or runtime-deletion
checks merely to manufacture a green timing row.
