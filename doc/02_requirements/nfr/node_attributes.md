# Node attributes: nonfunctional requirements

Date: 2026-11-06. Status: acceptance gates, not measured results.
Applies to the selected [full feature](../feature/node_attributes.md).

| ID | Target | Verification mechanism |
|---|---|---|
| NFR-001 | No weakening of initialization, lifetime, ownership, visibility, bounds or topology checks in release or observer-off builds. | Differential positive/negative corpus, release artifacts, stale-handle and failure injection. |
| NFR-002 | Disabled ordinary programs generate no managed schema tables, managed helpers or data-observer dependencies. | Compare normalized generated IR/symbol/dependency inventories; allow incidental build metadata differences, not semantic/code additions. |
| NFR-003 | A ready managed read performs no schema scan, full-node initialization scan, SDN parse, filesystem operation, string selector matching, blocking profile lock or storage migration. | Inspect lowered access and execute counters/instrumented workloads proving the forbidden work is absent. |
| NFR-004 | Schema/policy resolution occurs once per compilation context; descriptors are immutable and worker-shareable, with exact invalidation. | Two concurrent builds with conflicting schemas/profiles, input changes and stale receipts. No ambient process-global catalog authority. |
| NFR-005 | Resolve declarations deterministically in O(d log d + e) comparison work after type resolution, where d is declaration count and e is applicability/dependency edges; access is O(1) for qualified dense projections. | Scaling fixtures and operation counts; sparse/hash and topology checks disclose their separate complexity and limits. |
| NFR-006 | Capture buffers/counters have configured finite bounds; overflow/drop is observable; callbacks never wait, migrate, or allocate unbounded storage. | Saturation/reentrancy tests, allocation and synchronization evidence, loss accounting. |
| NFR-007 | Default adoption is next-build/instance/snapshot; conversion peak budget includes old/new storage, indexes, temporary buffers and retained epochs. | OOM/cancellation/reader-retention tests; rejected migration leaves old root authoritative. |
| NFR-008 | Measure disabled, prepared-disabled and active modes separately on the same workload and admitted binary lineage. | Cold/warm parse/resolve/lower and BuildRunner comparisons; wall time, throughput, p50/p95/p99 where meaningful, peak RSS, code size and allocations. |
| NFR-009 | No performance promotion without a recorded acceptance budget and reproducible comparison against baseline. | Before L3 rollout, record target-specific latency/RSS/size budgets and sample protocol in the implementation receipt. Unknown costs are not a speedup. Structural landing does not invent numerical results. |
| NFR-010 | New production implementation stays pure Simple and respects existing layer/owner boundaries. | Import/visibility review, no private-array copies, existing direct-env/process guards, full required compiler/lib/MCP checks. |
| NFR-011 | All semantic decisions are reproducible from exact source/schema/policy/target/planner/profile identities. | Reordered equivalent inputs yield the same semantic plan; changed consumed facts invalidate affected artifacts; provenance remains inspectable. |
| NFR-012 | No verification using a Rust seed disguised as a self-hosted runtime. | Record admitted executable path, hash, stage, lineage, command and exit/test counts. Missing admission is TEST_BLOCKED. |

Coverage target is at least 80% branch coverage of new logic with explicit
initialization, failure, lifetime and off-mode cases. A numeric coverage value
cannot replace the requirement-to-scenario matrix or native/interpreter parity.
