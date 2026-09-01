# Backend Software Simd Span Source Specification

> Tests covering SoftwareBackend in-place SIMD blend spans.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Software Simd Span Source Specification

## Scenarios

### SoftwareBackend in-place SIMD blend spans

#### blends an opaque source span over the destination in place

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- blend opaque pixels, assert exact source-over output
   - Expected: out[0] equals `0xFFAABBCCu32`
   - Expected: out[1] equals `0xFF112233u32`
   - Expected: out[2] equals `0xFF0000FFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("blend opaque pixels, assert exact source-over output")
val dst = [0xFF00FF00u32, 0xFFFF0000u32, 0xFF102030u32]
val src = [0xFFAABBCCu32, 0xFF112233u32, 0xFF0000FFu32]
val out = rt_engine2d_simd_blend_span_u32(dst, 0, src, 0, 3)
expect(out[0]).to_equal(0xFFAABBCCu32)
expect(out[1]).to_equal(0xFF112233u32)
expect(out[2]).to_equal(0xFF0000FFu32)
```

</details>

#### keeps fully transparent source pixels untouched

- blend zero-alpha pixels, assert destination preserved
   - Expected: out[0] equals `0xFF123456u32`
   - Expected: out[1] equals `0xFF00FF00u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("blend zero-alpha pixels, assert destination preserved")
val dst = [0xFF123456u32, 0xFF00FF00u32]
val src = [0x00FFFFFFu32, 0x00112233u32]
val out = rt_engine2d_simd_blend_span_u32(dst, 0, src, 0, 2)
expect(out[0]).to_equal(0xFF123456u32)
expect(out[1]).to_equal(0xFF00FF00u32)
```

</details>

#### computes the 255-denominator partial blend exactly

- blend half-alpha red over opaque blue, assert exact channels
   - Expected: out[0] equals `0xFF7F0080u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("blend half-alpha red over opaque blue, assert exact channels")
val dst = [0xFFFF0000u32]
val src = [0x800000FFu32]
val out = rt_engine2d_simd_blend_span_u32(dst, 0, src, 0, 1)
# sa=128 inv=127: r=(0*128+255*127)/255=127, g=0, b=(255*128+0*127)/255=128
expect(out[0]).to_equal(0xFF7F0080u32)
```

</details>

#### fills a constant span through the const-span route

- const-blend an opaque color over a cleared span
   - Expected: out[0] equals `0x00000000u32`
   - Expected: out[1] equals `0xFFABCDEFu32`
   - Expected: out[2] equals `0xFFABCDEFu32`
   - Expected: out[3] equals `0x00000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("const-blend an opaque color over a cleared span")
val dst = [0x00000000u32, 0x00000000u32, 0x00000000u32, 0x00000000u32]
val out = rt_engine2d_simd_blend_const_span_u32(dst, 1, 2, 0xFFABCDEFi64)
expect(out[0]).to_equal(0x00000000u32)
expect(out[1]).to_equal(0xFFABCDEFu32)
expect(out[2]).to_equal(0xFFABCDEFu32)
expect(out[3]).to_equal(0x00000000u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/backend_software_simd_span_source_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SoftwareBackend in-place SIMD blend spans.
- SoftwareBackend in-place SIMD blend spans

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

- Canonical SPipe generation for source `4e5216d95bb7a2fd46ece04efd9e01900bebeb6d51ec2a655c1ae7540a93fbd1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e5216d95bb7a2fd46ece04efd9e01900bebeb6d51ec2a655c1ae7540a93fbd1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e5216d95bb7a2fd46ece04efd9e01900bebeb6d51ec2a655c1ae7540a93fbd1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gpu/engine2d/backend_software_simd_span_source_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/backend_software_simd_span_source_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/backend_software_simd_span_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/backend_software_simd_span_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/backend_software_simd_span_source_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blends an opaque source span over the destination in place' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/backend_software_simd_span_source_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps fully transparent source pixels untouched' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/backend_software_simd_span_source_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes the 255-denominator partial blend exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
