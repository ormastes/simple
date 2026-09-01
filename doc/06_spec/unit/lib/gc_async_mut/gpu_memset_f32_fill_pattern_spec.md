# Gpu Memset F32 Fill Pattern Specification

> Tests covering gpu_memset_f32 fill pattern.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Memset F32 Fill Pattern Specification

## Scenarios

### gpu_memset_f32 fill pattern

#### produces the IEEE-754 bit pattern of 3.14f

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces the IEEE-754 bit pattern of 3.14f


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces the IEEE-754 bit pattern of 3.14f")
# The value from the filed bug: 0x4048F5C3 is not byte-uniform, which is
# why the byte-granularity path could never express it.
assert_equal(gpu_f32_fill_pattern(3.14 as f32), 1078523331)
```

</details>

#### produces the IEEE-754 bit pattern for exact binary values

- produces the IEEE-754 bit pattern for exact binary values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces the IEEE-754 bit pattern for exact binary values")
assert_equal(gpu_f32_fill_pattern(1.0 as f32), 1065353216)
assert_equal(gpu_f32_fill_pattern(0.5 as f32), 1056964608)
assert_equal(gpu_f32_fill_pattern(-2.0 as f32), 3221225472)
```

</details>

#### is a bitcast, not a numeric conversion

- is a bitcast, not a numeric conversion


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is a bitcast, not a numeric conversion")
# -0.0 numerically equals 0.0 but has a different bit pattern. A cast
# would collapse these; a bitcast must not.
assert_equal(gpu_f32_fill_pattern(0.0 as f32), 0)
assert_equal(gpu_f32_fill_pattern(-0.0 as f32), 2147483648)
```

</details>

#### does not discard the value (the regression)

- does not discard the value (the regression)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not discard the value (the regression)")
# The defect returned a zero fill word regardless of input. Any two
# distinct floats must give distinct, non-zero patterns.
val a = gpu_f32_fill_pattern(3.14 as f32)
val b = gpu_f32_fill_pattern(1.0 as f32)
assert_not_equal(a, b)
assert_not_equal(a, 0)
```

</details>

#### leaves the i32 fill pattern alone (control)

- leaves the i32 fill pattern alone (control)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves the i32 fill pattern alone (control)")
# Control: passes both before and after, showing the suite is not
# uniformly red and that the sibling i32 path is untouched.
assert_equal(gpu_i32_fill_pattern(1), 1)
assert_equal(gpu_i32_fill_pattern(-1), 4294967295)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/gpu_memset_f32_fill_pattern_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gpu_memset_f32 fill pattern.
- gpu_memset_f32 fill pattern

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

- Canonical SPipe generation for source `163e3301de175133ab4212f29be42b47877206c9206a9b7643d2b4e9c3c851d5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `163e3301de175133ab4212f29be42b47877206c9206a9b7643d2b4e9c3c851d5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `163e3301de175133ab4212f29be42b47877206c9206a9b7643d2b4e9c3c851d5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/gc_async_mut/gpu_memset_f32_fill_pattern_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/gpu_memset_f32_fill_pattern_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/gpu_memset_f32_fill_pattern_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/gpu_memset_f32_fill_pattern_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/gpu_memset_f32_fill_pattern_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces the IEEE-754 bit pattern of 3.14f' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/gpu_memset_f32_fill_pattern_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces the IEEE-754 bit pattern for exact binary values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/gpu_memset_f32_fill_pattern_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is a bitcast, not a numeric conversion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
