# Placement Backends Specification

> Tests covering Placement backend and planner contracts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Placement Backends Specification

## Scenarios

### Placement backend and planner contracts

#### should keep planner output deterministic under request reorder

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should keep planner output deterministic under request reorder
   - Expected: plan_a.receipt_seed.value equals `plan_b.receipt_seed.value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should keep planner output deterministic under request reorder")
val ordered = [request(2, 12), request(1, 9), request(3, 3)]
val shuffled = [request(3, 3), request(1, 9), request(2, 12)]
val plan_a = make_deterministic_plan(ordered, sample_budget())
val plan_b = make_deterministic_plan(shuffled, sample_budget())
expect(plan_a.receipt_seed.value).to_equal(plan_b.receipt_seed.value)
```

</details>

#### should cap staged prefetch bytes by the ring budget

- should cap staged prefetch bytes by the ring budget
   - Expected: receipt.bytes_transferred equals `256`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should cap staged prefetch bytes by the ring budget")
val backend = StagedPlacementBackend.with_budget(256, 1024)
val prefetch = backend.prefetch(staged_plan(sample_budget()))
match prefetch:
    case Result.Ok(receipt):
        expect(receipt.bytes_transferred).to_equal(256)
    case Result.Err(_):
        expect(false).to_equal(true)
```

</details>

#### should keep direct backend capability explicit and fail closed when unsupported

- should keep direct backend capability explicit and fail closed when unsupported
   - Expected: receipt.backend equals `direct`
   - Expected: receipt.error equals ``
   - Expected: false is true
   - Expected: false is true
   - Expected: err equals `PlacementError.Unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should keep direct backend capability explicit and fail closed when unsupported")
val backend = DirectPlacementBackend()
val preflight = backend.probe().available
val prefetch = backend.prefetch(staged_plan(sample_budget()))
if preflight:
    match prefetch:
        case Result.Ok(receipt):
            expect(receipt.backend).to_equal("direct")
            expect(receipt.error).to_equal("")
        case Result.Err(_):
            expect(false).to_equal(true)
else:
    match prefetch:
        case Result.Ok(_):
            expect(false).to_equal(true)
        case Result.Err(err):
            expect(err).to_equal(PlacementError.Unsupported)
```

</details>

#### should keep device-initiated backend behind an explicit experimental gate

- should keep device-initiated backend behind an explicit experimental gate
   - Expected: false is true
   - Expected: err equals `PlacementError.Unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should keep device-initiated backend behind an explicit experimental gate")
val backend = DeviceInitiatedPlacementBackend()
expect(backend.probe().available).to_equal(
    env_get("SIMPLE_MMU_DEVICE_INITIATED_BACKEND") == "1"
)
val acquired = backend.acquire(staged_plan(sample_budget()))
match acquired:
    case Result.Ok(_):
        expect(false).to_equal(true)
    case Result.Err(err):
        expect(err).to_equal(PlacementError.Unsupported)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/placement_backends/placement_backends_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Placement backend and planner contracts.
- Placement backend and planner contracts

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a43b8d6f6ae2730f8ed2bb86905b4f499984a43413de94d92e8ae1e1c4076dcd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a43b8d6f6ae2730f8ed2bb86905b4f499984a43413de94d92e8ae1e1c4076dcd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a43b8d6f6ae2730f8ed2bb86905b4f499984a43413de94d92e8ae1e1c4076dcd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/01_unit/lib/nogc_async_mut/gpu/placement_backends/placement_backends_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/gpu/placement_backends/placement_backends_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=80 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/gpu/placement_backends/placement_backends_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/gpu/placement_backends/placement_backends_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/gpu/placement_backends/placement_backends_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/gpu/placement_backends/placement_backends_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep planner output deterministic under request reorder' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/nogc_async_mut/gpu/placement_backends/placement_backends_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep planner output deterministic under request reorder' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/gpu/placement_backends/placement_backends_spec.spl:72:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should cap staged prefetch bytes by the ring budget' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/nogc_async_mut/gpu/placement_backends/placement_backends_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should cap staged prefetch bytes by the ring budget' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/gpu/placement_backends/placement_backends_spec.spl:83:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep direct backend capability explicit and fail closed when unsupported' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/nogc_async_mut/gpu/placement_backends/placement_backends_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep direct backend capability explicit and fail closed when unsupported' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/gpu/placement_backends/placement_backends_spec.spl:103:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep device-initiated backend behind an explicit experimental gate' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
