# MC/DC bounded report V2 performance evidence

Revision-under-test: dedicated `mcdc-hal` working copy, 2026-08-22.

Command: `sh scripts/check/check-mcdc-native-runtime-perf.shs`

| Path | Iterations | Time/op | Heap allocations | Workspace | Peak RSS |
|---|---:|---:|---:|---:|---:|
| V1 report baseline | 100,000 | 5,176 ns | 0 | 512 B | 1,280 KiB process peak |
| V2 complete report | 100,000 | 10,736 ns | 0 | 824 B | 1,280 KiB process peak |
| V2 two-process merge | 100,000 | 6,960 ns | 0 | 880 B | 1,280 KiB process peak |

The V2 delta is the bounded integrity and completeness work absent from V1:
source-span decision rows, decision totals, binary/process identity, row SHA-256,
and complete-report SHA-256. The merge is deterministic O(N), scans each input
row once, uses register masks and fixed caller output, and performs no heap
allocation. The retained gate is 100,000 ns/op and 65,536 KiB peak RSS.
The first V2 measurement was 12,749 ns/report; removing a redundant second
manifest authentication pass reduced it to 10,736 ns/report (15.8%) while the
V1 owner remains the single manifest validator.

The sharded collector check in the same run retained 9,472 KiB peak RSS and
zero hot-path heap allocations. Binary/result hashes are retained in
`build/mcdc-native-runtime-perf/identity.tsv` for the local evidence bundle.

The Simple optimizer was not run: the admitted self-hosted Simple compiler is
currently unavailable for this branch, and the Rust seed is explicitly not an
acceptable substitute. This native ABI path was instead compiled with `cc
-std=c11 -O2 -Wall -Wextra -Werror -pedantic` by the canonical focused gate.
