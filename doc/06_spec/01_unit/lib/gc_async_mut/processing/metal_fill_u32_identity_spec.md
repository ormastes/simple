# Metal Fill U32 Identity Specification

> Tests covering Metal ProcessingIR device identity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Metal Fill U32 Identity Specification

## Scenarios

### Metal ProcessingIR device identity

#### derives a stable identity from device metadata rather than a buffer handle

- derives a stable identity from device metadata rather than a buffer handle
   - Expected: repeated equals `first`
   - Expected: processing_metal_device_identity("", 8589934592) equals `0`
   - Expected: processing_metal_device_identity("Test Metal GPU", 0) equals `0`
   - Expected: processing_metal_device_identity("Test Metal GPU", -1) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("derives a stable identity from device metadata rather than a buffer handle")
val first = processing_metal_device_identity("Test Metal GPU", 8589934592)
val repeated = processing_metal_device_identity("Test Metal GPU", 8589934592)
val other_device = processing_metal_device_identity("Other Metal GPU", 8589934592)
val other_memory = processing_metal_device_identity("Test Metal GPU", 4294967296)

expect(first).to_be_greater_than(0)
expect(repeated).to_equal(first)
assert_not_equal(other_device, first)
assert_not_equal(other_memory, first)
expect(processing_metal_device_identity("", 8589934592)).to_equal(0)
expect(processing_metal_device_identity("Test Metal GPU", 0)).to_equal(0)
expect(processing_metal_device_identity("Test Metal GPU", -1)).to_equal(0)
expect(processing_metal_device_identity("Test Metal GPU", 9223372036854775807)).to_be_greater_than(0)
```

</details>

#### rejects invalid IR before any Metal device operation

- rejects invalid IR before any Metal device operation
   - Expected: zero.reason equals `invalid-element-count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects invalid IR before any Metal device operation")
val zero = processing_ir_execute_metal(processing_ir_fill_u32(0, 7u32))
expect(zero.reason).to_equal("invalid-element-count")
_expect_rejected(zero, "invalid-element-count")
_expect_rejected(processing_ir_execute_metal(processing_ir_fill_u32(536870912, 7u32)), "output-size-overflow")
_expect_rejected(processing_ir_execute_metal(ProcessingIr(op: 99, element_count: 1, value: 7u32, width: 1, height: 1, stride: 1, x: 0, y: 0, rect_width: 1, rect_height: 1)), "unsupported-op")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/processing/metal_fill_u32_identity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Metal ProcessingIR device identity.
- Metal ProcessingIR device identity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `c2c1b0b17ad8f7dd2a119027f8e6aac0ca32f74b93dead1630f17071803eae2a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c2c1b0b17ad8f7dd2a119027f8e6aac0ca32f74b93dead1630f17071803eae2a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c2c1b0b17ad8f7dd2a119027f8e6aac0ca32f74b93dead1630f17071803eae2a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/processing/metal_fill_u32_identity_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/processing/metal_fill_u32_identity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/processing/metal_fill_u32_identity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/processing/metal_fill_u32_identity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/processing/metal_fill_u32_identity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/processing/metal_fill_u32_identity_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives a stable identity from device metadata rather than a buffer handle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/processing/metal_fill_u32_identity_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid IR before any Metal device operation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
