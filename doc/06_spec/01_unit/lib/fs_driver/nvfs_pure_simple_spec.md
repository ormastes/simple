# Nvfs Pure Simple Specification

> Tests covering nvfs_pure_simple, alloc_zeroed_bytes, text_to_bytes_pure.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvfs Pure Simple Specification

## Scenarios

### nvfs_pure_simple

### alloc_zeroed_bytes

#### AC-3: alloc_zeroed_bytes(64) returns array of length 64

- AC-3: alloc_zeroed_bytes(64) returns array of length 64


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: alloc_zeroed_bytes(64) returns array of length 64")
val buf = alloc_zeroed_bytes(64)
expect buf.len == 64
```

</details>

#### AC-3: alloc_zeroed_bytes(64) first element is zero

- AC-3: alloc_zeroed_bytes(64) first element is zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: alloc_zeroed_bytes(64) first element is zero")
val buf = alloc_zeroed_bytes(64)
expect buf[0] == 0
```

</details>

#### AC-3: alloc_zeroed_bytes(64) last element is zero

- AC-3: alloc_zeroed_bytes(64) last element is zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: alloc_zeroed_bytes(64) last element is zero")
val buf = alloc_zeroed_bytes(64)
expect buf[63] == 0
```

</details>

#### AC-3: alloc_zeroed_bytes(0) returns empty array

- AC-3: alloc_zeroed_bytes(0) returns empty array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: alloc_zeroed_bytes(0) returns empty array")
val buf = alloc_zeroed_bytes(0)
expect buf.len == 0
```

</details>

#### AC-3: alloc_zeroed_bytes(1) returns single-element zero array

- AC-3: alloc_zeroed_bytes(1) returns single-element zero array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: alloc_zeroed_bytes(1) returns single-element zero array")
val buf = alloc_zeroed_bytes(1)
expect buf.len == 1
```

</details>

#### AC-3: alloc_zeroed_bytes(1) single element is zero

- AC-3: alloc_zeroed_bytes(1) single element is zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: alloc_zeroed_bytes(1) single element is zero")
val buf = alloc_zeroed_bytes(1)
expect buf[0] == 0
```

</details>

### text_to_bytes_pure

#### AC-3: text_to_bytes_pure(\

- AC-3: text_to_bytes_pure(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: text_to_bytes_pure(\")
val bytes = text_to_bytes_pure("ABC")
expect bytes.len == 3
```

</details>

#### AC-3: text_to_bytes_pure(\

- AC-3: text_to_bytes_pure(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: text_to_bytes_pure(\")
val bytes = text_to_bytes_pure("ABC")
expect bytes[0] == 65
```

</details>

#### AC-3: text_to_bytes_pure(\

- AC-3: text_to_bytes_pure(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: text_to_bytes_pure(\")
val bytes = text_to_bytes_pure("ABC")
expect bytes[1] == 66
```

</details>

#### AC-3: text_to_bytes_pure(\

- AC-3: text_to_bytes_pure(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: text_to_bytes_pure(\")
val bytes = text_to_bytes_pure("ABC")
expect bytes[2] == 67
```

</details>

#### AC-3: text_to_bytes_pure(\

- AC-3: text_to_bytes_pure(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: text_to_bytes_pure(\")
val bytes = text_to_bytes_pure("")
expect bytes.len == 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/fs_driver/nvfs_pure_simple_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nvfs_pure_simple, alloc_zeroed_bytes, text_to_bytes_pure.
- nvfs_pure_simple
- alloc_zeroed_bytes
- text_to_bytes_pure

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `abdbb77ca396c6331e543f033c1000cec0592de0cbce055ff8b3e05eab23dcaa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `abdbb77ca396c6331e543f033c1000cec0592de0cbce055ff8b3e05eab23dcaa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `abdbb77ca396c6331e543f033c1000cec0592de0cbce055ff8b3e05eab23dcaa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/fs_driver/nvfs_pure_simple_spec.spl
mirror: doc/06_spec/01_unit/lib/fs_driver/nvfs_pure_simple_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/fs_driver/nvfs_pure_simple_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/fs_driver/nvfs_pure_simple_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/fs_driver/nvfs_pure_simple_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: alloc_zeroed_bytes(64) returns array of length 64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/fs_driver/nvfs_pure_simple_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: alloc_zeroed_bytes(64) first element is zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/fs_driver/nvfs_pure_simple_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: alloc_zeroed_bytes(64) last element is zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
