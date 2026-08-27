# Ide Capabilities Harden Specification

> Tests covering capabilities: all registered entries have valid required fields.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ide Capabilities Harden Specification

## Scenarios

### capabilities: all registered entries have valid required fields

#### all capabilities pass ide_capability_valid

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- all capabilities pass ide_capability_valid
   - Expected: ide_capability_valid_count() equals `ide_capability_count()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all capabilities pass ide_capability_valid")
expect(ide_capability_valid_count()).to_equal(ide_capability_count())
```

</details>

#### preview bounds with positive width and height are valid

- preview bounds with positive width and height are valid
   - Expected: ide_preview_bounds_valid(800, 600) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preview bounds with positive width and height are valid")
expect(ide_preview_bounds_valid(800, 600)).to_equal(true)
```

</details>

#### preview bounds with zero width are invalid

- preview bounds with zero width are invalid
   - Expected: ide_preview_bounds_valid(0, 600) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preview bounds with zero width are invalid")
expect(ide_preview_bounds_valid(0, 600)).to_equal(false)
```

</details>

#### preview bounds with zero height are invalid

- preview bounds with zero height are invalid
   - Expected: ide_preview_bounds_valid(800, 0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preview bounds with zero height are invalid")
expect(ide_preview_bounds_valid(800, 0)).to_equal(false)
```

</details>

#### preview bounds with negative dimensions are invalid

- preview bounds with negative dimensions are invalid
   - Expected: ide_preview_bounds_valid(-1, -1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preview bounds with negative dimensions are invalid")
expect(ide_preview_bounds_valid(-1, -1)).to_equal(false)
```

</details>

#### capability count is positive

- capability count is positive
   - Expected: ide_capability_count() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("capability count is positive")
expect(ide_capability_count() > 0).to_equal(true)
```

</details>

#### capability ids are all non-empty via ide_capability_valid

- capability ids are all non-empty via ide_capability_valid
   - Expected: all_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("capability ids are all non-empty via ide_capability_valid")
var all_ok = true
for cap in ide_capabilities():
    if not ide_capability_valid(cap):
        all_ok = false
expect(all_ok).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ide/ide_capabilities_harden_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering capabilities: all registered entries have valid required fields.
- capabilities: all registered entries have valid required fields

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `6b92c2877332244f983805112479408d7229a5e77a21084743f6505f97e3d0e1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6b92c2877332244f983805112479408d7229a5e77a21084743f6505f97e3d0e1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6b92c2877332244f983805112479408d7229a5e77a21084743f6505f97e3d0e1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/ide/ide_capabilities_harden_spec.spl
mirror: doc/06_spec/01_unit/app/ide/ide_capabilities_harden_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/ide/ide_capabilities_harden_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ide/ide_capabilities_harden_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ide/ide_capabilities_harden_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all capabilities pass ide_capability_valid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ide/ide_capabilities_harden_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preview bounds with positive width and height are valid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ide/ide_capabilities_harden_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preview bounds with zero width are invalid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
