# Ide Slides Harden Specification

> Tests covering slides_compat: empty presentation does not crash.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ide Slides Harden Specification

## Scenarios

### slides_compat: empty presentation does not crash

#### empty presentation probe returns non-negative slide count

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- empty presentation probe returns non-negative slide count
   - Expected: probe.slide_count >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty presentation probe returns non-negative slide count")
val probe = ide_slide_compat_probe_empty()
expect(probe.slide_count >= 0).to_equal(true)
```

</details>

#### empty presentation outline_line_count is non-negative

- empty presentation outline_line_count is non-negative
   - Expected: probe.outline_line_count >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty presentation outline_line_count is non-negative")
val probe = ide_slide_compat_probe_empty()
expect(probe.outline_line_count >= 0).to_equal(true)
```

</details>

#### empty presentation design_count is non-negative

- empty presentation design_count is non-negative
   - Expected: probe.design_count >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty presentation design_count is non-negative")
val probe = ide_slide_compat_probe_empty()
expect(probe.design_count >= 0).to_equal(true)
```

</details>

#### sample presentation has at least one slide

- sample presentation has at least one slide
   - Expected: probe.slide_count > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sample presentation has at least one slide")
val probe = ide_slide_compat_probe()
expect(probe.slide_count > 0).to_equal(true)
```

</details>

#### sample presentation thumbnail is non-empty

- sample presentation thumbnail is non-empty
   - Expected: probe.thumbnail.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sample presentation thumbnail is non-empty")
val probe = ide_slide_compat_probe()
expect(probe.thumbnail.len() > 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ide/ide_slides_harden_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering slides_compat: empty presentation does not crash.
- slides_compat: empty presentation does not crash

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

- Canonical SPipe generation for source `27dd041e3e82a1d8fb99b23f2fc3a1e57817f583f658a7b6687e8ded3d40a709`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `27dd041e3e82a1d8fb99b23f2fc3a1e57817f583f658a7b6687e8ded3d40a709`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `27dd041e3e82a1d8fb99b23f2fc3a1e57817f583f658a7b6687e8ded3d40a709`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/ide/ide_slides_harden_spec.spl
mirror: doc/06_spec/01_unit/app/ide/ide_slides_harden_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/ide/ide_slides_harden_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ide/ide_slides_harden_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ide/ide_slides_harden_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty presentation probe returns non-negative slide count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ide/ide_slides_harden_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty presentation outline_line_count is non-negative' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ide/ide_slides_harden_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty presentation design_count is non-negative' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
