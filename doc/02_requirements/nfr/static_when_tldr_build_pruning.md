# Static condition and build-pruning nonfunctional requirements

Status: proposed implementation budgets for the selected feature; no measured speedup yet.

| ID | Budget/invariant | Measurement |
|---|---|---|
| NFR-001 | No-directive/no-summary-static-if file: at most one extra linear byte/SIMD pre-scan, no guard stack/table allocation, TRUE sentinel. Reuse existing token pass when possible. | Allocation and scan counters, bytes read |
| NFR-002 | Structural scan O(bytes + emitted facts); no per-symbol rereads. Common conjunction operations bounded by small domain cardinality; DAG interning expected amortized O(1), with collision/work limits. | Scaled fixtures, counted visits/probes |
| NFR-003 | Guard evaluation O(unique visited nodes); closure O(reachable edges + evaluated guards), with bounded queue and SCC fixed points. | Node/edge visits and high-water marks |
| NFR-004 | Wire GuardId is four bytes; shared tables have explicit byte/item/depth limits; exhausting limits is a diagnostic or complete conservative fallback, never successful truncation. | Boundary and adversarial tests |
| NFR-005 | TLDR graph traversal O(entries + references + guards). Deterministic grouping/sorting may cost O(n log n); do not claim total linear time with comparison sorting. | Independent traversal/sort counters |
| NFR-006 | No AST/HIR shared mutability, no waiting job occupying compiler worker; bounded immutable jobs/results, parent-owned commits and lifetime fencing. | Native contention/closure tests; cache prerequisite gates |
| NFR-007 | False edges produce zero dependency candidate probes/reads/parses/build submissions. Distinguish parent source scanning from excluded dependency I/O. | Per-logical-module event trace and negative missing-module fixture |
| NFR-008 | Warm unchanged build avoids full parses/lowering when valid summaries/artifacts exist; source and CAS validation costs reported separately. No timestamp-only cache authority. | Cold/warm bytes/hash/decode/parse counters |
| NFR-009 | Paired native standalone/runner measurements report wall, CPU, max process-tree RSS, p50/p95 across bounded samples, identical producer/options/source. No-condition overhead target within 5% of baseline or measurement uncertainty; exceptions require explanation before default enablement. | Predeclared fixture/measurement manifest |
| NFR-010 | Near-zero/Go-like speed remains a benchmark goal. No absolute speed claim before measurements. GPU dispatch must beat scalar including transfers or choose scalar. | End-to-end timings including setup and I/O |

The 5% overhead threshold is a proposed calibration gate, not a user-promised performance result. Calibrate measurement noise before enablement. Initial proposed safety limits for implementation review: nesting 256; guard table 65,536 nodes; 262,144 reference facts per summary; encoded summary 16 MiB. These are versioned configurable resource limits, not language expressiveness promises. Maximum-input acceptance must measure total allocator/RSS costs rather than multiplying payload sizes and calling that RSS.

Do not repeatedly benchmark green criteria. Predeclare sample count inside one acceptance run, then at most three verify/fix cycles. Current diagnostic seed results cannot establish native performance. Native four-thread independent compiler contexts and ten-process contention remain prerequisites inherited from the cooperative cache feature; this design does not authorize enabling unsafe frontend globals.