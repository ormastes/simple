# Consumed Host retention assessment — authored manual

Status: NOT_RUN / NOT_GENERATED / NOT_QUALIFIED, 2026-11-15.

Source: [host_operation_retention_assessment_v3_spec.spl](../../../../../test/02_integration/lib/orchestration/host_operation_retention_assessment_v3_spec.spl).
These are executable source assertions, not runtime results. Fixtures acquire an
actual owned journal over existing canonical Host preparation data. A scripted
Container value remains unused; zero provider calls is asserted and does not
qualify native execution, service installation or machine admission.

| Scenario | Required observation | Evidence |
| --- | --- | --- |
| Canonical referenced payload | Actual owner returns exact existing intent-producer bytes at its selected revision/sequence; no provider effect or event append | NOT_RUN |
| Caller errors and file isolation | Invalid ID requests reject without poison; a business ID resembling a lease does not select that file; a valid subsequent request works | NOT_RUN |
| Sticky payload fault | Damage the actual referenced payload, detect mismatch, restore bytes and still reject the copied owner with the exact digest until close | NOT_RUN |
| Real status consumer | Existing `host-status` service includes aggregate Incomplete counts without raw IDs/records, preserves kind/sequence and invokes zero provider commands | NOT_RUN |
| Bounded deterministic sample | Five actual preparations in unsorted order select the expected smallest four; total/examined/omitted and validated payload counts remain explicit | NOT_RUN |
| Compatibility-only status | Legacy fixture receives unavailable owned assessment with zero examined and all omitted, retaining old status fields | NOT_RUN |

`Open the actual owned Host journal`, `Capture bounded owner-derived reservation
evidence`, and `Read the existing Host status service` are authored step labels,
not generated captures. No expiry, positive pin release, dedupe eviction or GC
permission follows from these diagnostics. True concurrency, Windows/fault and
durability checks, coverage, generated-manual maintenance and performance remain
NOT_COVERED/NOT_RUN. See the [design](../../../../05_design/daemon_operation_retention_assessment_v3.md).
