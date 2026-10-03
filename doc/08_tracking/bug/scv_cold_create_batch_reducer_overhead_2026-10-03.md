# SCV cold unique-create batch repeats full event reduction

Status: source optimization implemented; executable correctness and performance
verification pending. This is not a confirmed root cause of the reported cold
inventory timeout.

`compile_source_inventory_apply_and_publish_v1` sends cold rebuilds to
`compile_source_inventory_apply_cold_events_v1`. Before this change, even the
normal unique-create Git listing constructed a singleton inventory and invoked
the full per-event reducer for every source. The existing pure initializer
already validates exactly this restricted batch and sorts the final entries.

The cold reducer now uses that initializer when admitted, preserves
`initial_generation + event_count` and changed flags, and returns immediately.
Its original fallback remains responsible for duplicate identity semantics,
delete/modify churn, invalid-row diagnostics and generation-overflow behavior.
No admission check, source scope, receipt, pointer, cache or lock is bypassed.

Test-first commit `e836aff49f2` adds five cases to the existing cold reducer
suite, including canonical-byte comparisons against serial replay and exact
generation/flag boundaries. The initializer's existing tests remain relevant.
No executable RED/GREEN or timing result has been observed.

Current source uses indexed reduction, heap sorting and coalesced facet hashing;
there is no evidence that this particular path is quadratic on the diagnostic
native binary. That binary's adjacent provenance/admission receipts were absent,
so matching its implementation to this source is not established. The prior
three diagnostic attempts remain exhausted and were not rerun.

Next verification should use an admitted producer and the existing SCV resource
profile N/2N collector/spec, retaining semantic digests and raw CPU/RSS/timing.
The inventory owner currently exposes no existing cheap structured phase-timing
surface; this change therefore adds no new logging/env facade or per-file logs.
Phase attribution remains a separate prerequisite before claiming the timeout's
dominant cause or attempting another end-to-end build.
