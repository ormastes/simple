# Attributes Specification

> Tests covering FunctionAttr, parse_function_attrs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Attributes Specification

## Scenarios

### FunctionAttr

### parse_function_attrs

#### parses bare fast_math

- parses bare fast_math
   - Expected: fa.has_fast_math is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses bare fast_math")
val fa = parse_function_attrs([make_attr("fast_math")])
expect(fa.has_fast_math).to_equal(true)
```

</details>

#### parses bare simd as enabled

- parses bare simd as enabled
   - Expected: fa.is_simd is true
   - Expected: fa.simd_enable is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses bare simd as enabled")
val fa = parse_function_attrs([make_attr("simd")])
expect(fa.is_simd).to_equal(true)
expect(fa.simd_enable).to_equal(true)
```

</details>

#### parses simd(disable)

- parses simd(disable)
   - Expected: fa.is_simd is true
   - Expected: fa.simd_disable is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses simd(disable)")
val fa = parse_function_attrs([make_simd_attr("disable")])
expect(fa.is_simd).to_equal(true)
expect(fa.simd_disable).to_equal(true)
```

</details>

#### parses simd(prefer_scalable)

- parses simd(prefer_scalable)
   - Expected: fa.is_simd is true
   - Expected: fa.simd_prefer_scalable is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses simd(prefer_scalable)")
val fa = parse_function_attrs([make_simd_attr("prefer_scalable")])
expect(fa.is_simd).to_equal(true)
expect(fa.simd_prefer_scalable).to_equal(true)
```

</details>

#### default function attrs leave fast_math false

- default function attrs leave fast_math false
   - Expected: fa.has_fast_math is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default function attrs leave fast_math false")
val fa = FunctionAttr.default()
expect(fa.has_fast_math).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/common/attributes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FunctionAttr, parse_function_attrs.
- FunctionAttr
- parse_function_attrs

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

- Canonical SPipe generation for source `fc64f27c65cda2d8637215c6f47f929a2bdb23030a12fdc6d2092257b0226ad5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fc64f27c65cda2d8637215c6f47f929a2bdb23030a12fdc6d2092257b0226ad5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fc64f27c65cda2d8637215c6f47f929a2bdb23030a12fdc6d2092257b0226ad5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/common/attributes_spec.spl
mirror: doc/06_spec/unit/compiler/common/attributes_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/common/attributes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/common/attributes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/common/attributes_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses bare fast_math' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/common/attributes_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses bare simd as enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/common/attributes_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses simd(disable)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
