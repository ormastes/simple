# MC/DC report V2 CLI performance and memory evidence — 2026-08-22

Command: `sh scripts/check/check-mcdc-native-runtime-perf.shs` using the same
`-O2` native selfcheck and `/usr/bin/time` RSS measurement before and after the
V2 CLI integration. The CLI itself is a cold-path formatter; the measured ABI
is the mission-critical allocation-free report/merge owner.

| Measurement | Retained baseline | After identity validation | Result |
|---|---:|---:|---|
| V2 report | 10,736 ns/report | 12,519 ns/report | 0 allocations |
| V2 merge | 6,960 ns/merge | 7,822 ns/merge | 0 allocations |
| Manifest selfcheck peak RSS | 1,280 KiB | 1,280 KiB | unchanged |
| Sharded collector peak RSS | 9,472 KiB | 9,472 KiB | unchanged |

The host was globally slower during the after sample: the unchanged V1 report
moved from 5,176 to 6,653 ns (+28.5%) and unrelated sharded throughput fell
from 28.4M to 10.6M events/s. Normalized to V1 in each run, V2 merge improved
from 1.345x to 1.176x. Therefore the wall-time delta does not demonstrate a
feature regression. The final source additionally hoists the 64-byte binary
identity syntax check from every input row to the first row; equality against
that admitted identity remains per row. No extra pass, allocation, copy, hash,
or dispatch was added to event collection.

Algorithmic review: report construction remains O(events log events + proof
work + decisions); the additive row materialization is O(decisions). Merge is
one O(input rows) scan after caller sorting. CLI reads and formats only bounded
fixed rows, checks the full output-line budget before formatting, and never
executes on the mission-critical record path.

The Simple optimizer was not run: this worktree's deployed self-hosted compiler
is not an admitted source-matched binary, and the recovery-cycle cap is already
exhausted. The Rust seed was not substituted. Native ABI and source-contract
checks remain stage-independent.
