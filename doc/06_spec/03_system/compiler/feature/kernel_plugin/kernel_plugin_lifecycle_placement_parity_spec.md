# KPF Lifecycle Placement Parity

This executable scenario proves REQ-KPF-007 across static, native, worker, and
optional Wasm placement adapters. All placements use one bounded lifecycle
owner for prepare, start, publish, drain, retire, and unload.

The crash-loop scenario consumes a bounded restart budget inside a fixed time
window, quarantines only the failed generation, leaves a sibling provider
published, rejects stale-generation faults, and resets fault state only when a
new generation is prepared. Receipts are monotonic, deterministic, and always
record `host_failed: false` for provider-local faults.

Mutation coverage rejects restart-budget bypass and stale-generation reuse.
