# Gpu Glass Specification

> Tests covering GpuCompositorBackend CompositorGlassCapable (D2 Phase 2 Gpu).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Glass Specification

## Scenarios

### GpuCompositorBackend CompositorGlassCapable (D2 Phase 2 Gpu)

#### as_glass_capable
_Backend opts back in to the glass subtrait in Phase 2 Gpu._

#### opts in (returns non-nil, unlike Phase 1)

- opts in (returns non-nil, unlike Phase 1)
   - Expected: cap != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opts in (returns non-nil, unlike Phase 1)")
"""Phase 1 returned nil; Phase 2 Gpu must return self."""
val backend = _make_backend()
val cap = backend.as_glass_capable()
expect(cap != nil).to_equal(true)
```

</details>

#### cap_blend_rect dispatch

#### type-checks against the Gpu backend

- type-checks against the Gpu backend
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("type-checks against the Gpu backend")
val backend = _make_backend()
if false:
    cap_blend_rect(backend, 0, 0, 4, 4, 0xFF7F7F7Fu32, 128u8)
expect(true).to_equal(true)
```

</details>

#### cap_blur_region dispatch

#### type-checks against the Gpu backend

- type-checks against the Gpu backend
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("type-checks against the Gpu backend")
val backend = _make_backend()
if false:
    cap_blur_region(backend, 0, 0, 4, 4, 2u32)
expect(true).to_equal(true)
```

</details>

#### cap_gradient_v dispatch

#### type-checks against the Gpu backend

- type-checks against the Gpu backend
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("type-checks against the Gpu backend")
val backend = _make_backend()
if false:
    cap_gradient_v(backend, 0, 0, 4, 4, 0xFF000000u32, 0xFFFFFFFFu32)
expect(true).to_equal(true)
```

</details>

#### cap_read_pixel dispatch

#### type-checks against the Gpu backend

- type-checks against the Gpu backend
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("type-checks against the Gpu backend")
val backend = _make_backend()
if false:
    val _px = cap_read_pixel(backend, 0, 0)
expect(true).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/compositor/gpu_glass_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GpuCompositorBackend CompositorGlassCapable (D2 Phase 2 Gpu).
- GpuCompositorBackend CompositorGlassCapable (D2 Phase 2 Gpu)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `219023f05694f157681de70c88a03faee9526c2438f581a87f083b434202bb23`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `219023f05694f157681de70c88a03faee9526c2438f581a87f083b434202bb23`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `219023f05694f157681de70c88a03faee9526c2438f581a87f083b434202bb23`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/compositor/gpu_glass_spec.spl
mirror: doc/06_spec/unit/os/compositor/gpu_glass_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/compositor/gpu_glass_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/compositor/gpu_glass_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/compositor/gpu_glass_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opts in (returns non-nil, unlike Phase 1)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/compositor/gpu_glass_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'type-checks against the Gpu backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/compositor/gpu_glass_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'type-checks against the Gpu backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
