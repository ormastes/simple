# Comprehension Specification

> Tests covering List comprehension.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Comprehension Specification

## Scenarios

### List comprehension

#### for-first basic

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- for-first basic
   - Expected: result equals `[2, 4, 6]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for-first basic")
val result = [for x in [1, 2, 3]: x * 2]
expect(result).to_equal([2, 4, 6])
```

</details>

#### for-first with filter

- for-first with filter
   - Expected: result equals `[4, 5]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for-first with filter")
val result = [for x in [1, 2, 3, 4, 5] if x > 3: x]
expect(result).to_equal([4, 5])
```

</details>

#### for-first with range

- for-first with range
   - Expected: result equals `[0, 1, 4, 9, 16]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for-first with range")
val result = [for i in 0..5: i * i]
expect(result).to_equal([0, 1, 4, 9, 16])
```

</details>

#### for-first with range and filter

- for-first with range and filter
   - Expected: result equals `[0, 2, 4, 6, 8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for-first with range and filter")
val result = [for i in 0..10 if i % 2 == 0: i]
expect(result).to_equal([0, 2, 4, 6, 8])
```

</details>

#### for-last basic

- for-last basic
   - Expected: result equals `[2, 4, 6]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for-last basic")
val result = [x * 2 for x in [1, 2, 3]]
expect(result).to_equal([2, 4, 6])
```

</details>

#### for-last with filter

- for-last with filter
   - Expected: result equals `[4, 5]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for-last with filter")
val result = [x for x in [1, 2, 3, 4, 5] if x > 3]
expect(result).to_equal([4, 5])
```

</details>

#### empty result from filter

- empty result from filter
   - Expected: result equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty result from filter")
val result = [for x in [1, 2, 3] if x > 10: x]
expect(result).to_equal([])
```

</details>

#### empty source array

- empty source array
   - Expected: result equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty source array")
var empty: [i64] = []
val result = [for x in empty: x * 2]
expect(result).to_equal([])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/parser/comprehension_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering List comprehension.
- List comprehension

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `f5bb435bf1bad7a0f81957abbb2af17112d02f336349c6189f820c3d0038751e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f5bb435bf1bad7a0f81957abbb2af17112d02f336349c6189f820c3d0038751e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f5bb435bf1bad7a0f81957abbb2af17112d02f336349c6189f820c3d0038751e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler_core/parser/comprehension_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/parser/comprehension_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/parser/comprehension_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/parser/comprehension_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/parser/comprehension_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'for-first basic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/parser/comprehension_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'for-first with filter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/parser/comprehension_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'for-first with range' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
