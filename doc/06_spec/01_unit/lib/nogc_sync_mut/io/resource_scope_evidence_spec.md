# Resource scope observation integrity

Requirement: ITEM4-REQ-009. Five authored executable scenarios in
`test/01_unit/lib/nogc_sync_mut/io/resource_scope_evidence_spec.spl`.
Status: **UNRUN**, manually authored companion; not generated execution evidence.

| Scenario | Observable contract |
|---|---|
| Strict counter parsing | Signs, decoration, absence and overflow reject; zero and the portable 2^60-1 boundary are preserved. |
| Systemd show parsing | Successful, nontruncated output requires Result, MemoryPeak and CPUUsageNSec. Failed process/runtime status, either truncated stream, missing properties and malformed numbers reject. |
| Missing/malformed cgroup peak | Real task-owned metric files are read by the production observation reader; absent or invalid memory.peak cannot become an available zero observation. |
| Valid cgroup peaks | Real files preserve zero, 65536 and the portable maximum, alongside independent CPU counters. |
| Invalid/inconsistent current charge | Malformed current charge and peak below current reject. |

Fixtures use secure unique directories and real writes, reads and cleanup.
They emulate metric file contents, not a mounted cgroup or enforcement authority.
The systemd parser is the production-used parsing seam; input strings do not
prove that a kernel scope existed. Missing setup records a failed assertion and
returns before dependent work.

Future execution with an independently admitted self-hosted runtime:
`<runtime> test test/01_unit/lib/nogc_sync_mut/io/resource_scope_evidence_spec.spl`

Still open: constrained worker attachment before workload allocation, enforced
whole-job hard cap and no-swap, descendant membership and cleanup, independent
kernel peak evidence, realistic workload RSS/performance, and full cancellation
and publication behavior. This repair does not qualify any worker or receipt.
