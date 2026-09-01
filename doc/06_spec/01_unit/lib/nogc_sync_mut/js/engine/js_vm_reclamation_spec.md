# js_vm_reclamation_spec

> Fail-fast design contract for generation-safe JavaScript VM ownership.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# js_vm_reclamation_spec

Fail-fast design contract for generation-safe JavaScript VM ownership.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/js/engine/js_vm_reclamation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Fail-fast design contract for generation-safe JavaScript VM ownership.

This spec is intentionally RED until the selected nogc_sync_mut engine exposes
the frozen JsHeapHandle, JsExternalRootKey, and JsTypedEdge ABI. It is not
runtime, GC-pause, RSS, or production-browser evidence.
The external production gate, not this contract, owns 10,000-cycle evidence.

## Scenarios

### JavaScript VM generation-safe ownership

### REQ-WEB-BROWSER-018: independent escaped ownership

#### retain equal escaped values for independent owners

- retain equal escaped values for independent owners
- Retain independent escaped values


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-WEB-BROWSER-017
# @req REQ-WEB-BROWSER-018
# @req REQ-SSPEC-LIB
step("retain equal escaped values for independent owners")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Retain independent escaped values")
val fixture = make_gc_ownership_fixture(
    "independent host, DOM, listener, Event, object, and closure owners",
    1000
)
expect_gc_ownership_invariants(fixture)
```

</details>

### REQ-WEB-BROWSER-017: complete typed graph

#### trace closure and host families without numeric guessing

- trace closure and host families without numeric guessing
- Trace typed closure roots


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("trace closure and host families without numeric guessing")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Trace typed closure roots")
val fixture = make_gc_ownership_fixture(
    "timers, promises, streams, iterators, WASM, DOM, and listeners",
    1000
)
expect_gc_ownership_invariants(fixture)
```

</details>

### REQ-WEB-BROWSER-018: generation-safe reuse

#### reject a stale owner release after its slot is reused

- reject a stale owner release after its slot is reused
- Reject stale releases after reuse


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reject a stale owner release after its slot is reused")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Reject stale releases after reuse")
val fixture = make_gc_ownership_fixture(
    "old generation release cannot affect the new occupant",
    1000
)
expect_gc_ownership_invariants(fixture)
```

</details>

### NFR-WEB-BROWSER-015/016: bounded linear work

#### preserve O(1) allocation counters across N, 2N, and cycles

- preserve O(1) allocation counters across N, 2N, and cycles
- Reclaim without allocation scans


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserve O(1) allocation counters across N, 2N, and cycles")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Reclaim without allocation scans")
val fixture = make_gc_ownership_fixture(
    "zero allocation scans and linear typed mark visits",
    1000
)
expect_gc_ownership_invariants(fixture)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-WEB-BROWSER-017`
- `REQ-WEB-BROWSER-018`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9fc86b88cf9e296f036c9b825d41c366dc2bd462ba7c93512f4bcfc23597694f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9fc86b88cf9e296f036c9b825d41c366dc2bd462ba7c93512f4bcfc23597694f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9fc86b88cf9e296f036c9b825d41c366dc2bd462ba7c93512f4bcfc23597694f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/nogc_sync_mut/js/engine/js_vm_reclamation_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/js/engine/js_vm_reclamation_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/01_unit/lib/nogc_sync_mut/js/engine/js_vm_reclamation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/js/engine/js_vm_reclamation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/js/engine/js_vm_reclamation_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
<!-- sspec-maintain:scorecard:end -->
