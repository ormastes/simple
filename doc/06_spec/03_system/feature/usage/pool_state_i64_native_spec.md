# Pool State I64 Native Specification

> Tests covering PoolStateV1 native scalar ownership.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pool State I64 Native Specification

## Scenarios

### PoolStateV1 native scalar ownership

#### keeps admission credit until joined results are released

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps admission credit until joined results are released
   - Expected: state.outstanding_count() equals `2`
   - Expected: full.status equals `POOL_SUBMIT_FULL_V1`
   - Expected: full.accepted() is false
   - Expected: first_joined.value equals `41`
   - Expected: first.release() is true
   - Expected: state.outstanding_count() equals `1`
   - Expected: second_joined.value equals `42`
   - Expected: second.release() is true
   - Expected: third_joined.value equals `43`
   - Expected: third.release() is true
   - Expected: state.close() is true
   - Expected: state.join_idle() is true
   - Expected: state.completed_count() equals `3`
   - Expected: state.outstanding_count() equals `0`
   - Expected: state.destroy() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps admission credit until joined results are released")
var state = PoolStateV1.create(2)
if not state.is_valid():
    fail("expected native PoolStateV1 state")

var first = require_accepted(state.try_submit_i64(plus_one, 40))
var second = require_accepted(state.try_submit_i64(plus_one, 41))
expect(state.outstanding_count()).to_equal(2)

val full = state.try_submit_i64(plus_one, 42)
expect(full.status).to_equal(POOL_SUBMIT_FULL_V1)
expect(full.accepted()).to_equal(false)

val first_joined = first.join()
if not first_joined.valid:
    fail("expected first PoolStateV1 result")
expect(first_joined.value).to_equal(41)
expect(first.release()).to_equal(true)
expect(state.outstanding_count()).to_equal(1)

var third = require_accepted(state.try_submit_i64(plus_one, 42))
val second_joined = second.join()
if not second_joined.valid:
    fail("expected second PoolStateV1 result")
expect(second_joined.value).to_equal(42)
expect(second.release()).to_equal(true)
val third_joined = third.join()
if not third_joined.valid:
    fail("expected third PoolStateV1 result")
expect(third_joined.value).to_equal(43)
expect(third.release()).to_equal(true)

expect(state.close()).to_equal(true)
expect(state.join_idle()).to_equal(true)
expect(state.completed_count()).to_equal(3)
expect(state.outstanding_count()).to_equal(0)
expect(state.destroy()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | Active |
| Source | `test/03_system/feature/usage/pool_state_i64_native_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering PoolStateV1 native scalar ownership.
- PoolStateV1 native scalar ownership

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `950b3cd7db42838bc134392f7e0ab0b7c6df6e1bbcba91841d8aa2d8c2dde631`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `950b3cd7db42838bc134392f7e0ab0b7c6df6e1bbcba91841d8aa2d8c2dde631`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `950b3cd7db42838bc134392f7e0ab0b7c6df6e1bbcba91841d8aa2d8c2dde631`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/feature/usage/pool_state_i64_native_spec.spl
mirror: doc/06_spec/03_system/feature/usage/pool_state_i64_native_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/pool_state_i64_native_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/pool_state_i64_native_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/pool_state_i64_native_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/pool_state_i64_native_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps admission credit until joined results are released' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
