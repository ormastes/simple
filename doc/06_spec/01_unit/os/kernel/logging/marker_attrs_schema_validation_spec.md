# Marker Attrs Schema Validation Specification

> Tests covering markers.validate enforces declared attrs_schema.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Marker Attrs Schema Validation Specification

## Scenarios

### markers.validate enforces declared attrs_schema

#### rejects '[vfs] mounted' with no attributes at all

- rejects '[vfs] mounted' with no attributes at all
   - Expected: result.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects '[vfs] mounted' with no attributes at all")
val result = validate("[vfs] mounted")
expect(result.is_ok()).to_equal(false)
```

</details>

#### rejects '[vfs] mounted' carrying only one of two declared keys

- rejects '[vfs] mounted' carrying only one of two declared keys
   - Expected: result.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects '[vfs] mounted' carrying only one of two declared keys")
val result = validate("[vfs] mounted device=vda")
expect(result.is_ok()).to_equal(false)
```

</details>

#### accepts '[vfs] mounted' with both declared keys present

- accepts '[vfs] mounted' with both declared keys present
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts '[vfs] mounted' with both declared keys present")
val result = validate("[vfs] mounted device=vda volume=ESP")
expect(result.is_ok()).to_equal(true)
```

</details>

#### still accepts a marker whose attrs_schema is empty

- still accepts a marker whose attrs_schema is empty
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still accepts a marker whose attrs_schema is empty")
val result = validate("[BOOT] entry")
expect(result.is_ok()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/logging/marker_attrs_schema_validation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering markers.validate enforces declared attrs_schema.
- markers.validate enforces declared attrs_schema

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ee9170fab83d2707400e8f116568fdc2e0398759a7162442227c7b86ec972f3e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee9170fab83d2707400e8f116568fdc2e0398759a7162442227c7b86ec972f3e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee9170fab83d2707400e8f116568fdc2e0398759a7162442227c7b86ec972f3e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/kernel/logging/marker_attrs_schema_validation_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/logging/marker_attrs_schema_validation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/logging/marker_attrs_schema_validation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/logging/marker_attrs_schema_validation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/logging/marker_attrs_schema_validation_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects '[vfs] mounted' with no attributes at all' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/logging/marker_attrs_schema_validation_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects '[vfs] mounted' carrying only one of two declared keys' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/logging/marker_attrs_schema_validation_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts '[vfs] mounted' with both declared keys present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
