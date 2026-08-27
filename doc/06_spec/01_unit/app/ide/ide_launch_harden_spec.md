# Ide Launch Harden Specification

> Tests covering launch_sanity: empty argv and unknown option handling.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ide Launch Harden Specification

## Scenarios

### launch_sanity: empty argv and unknown option handling

#### empty argv parse does not crash

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- empty argv parse does not crash
   - Expected: ide_launch_empty_argv_safe() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty argv parse does not crash")
expect(ide_launch_empty_argv_safe()).to_equal(true)
```

</details>

#### unknown-only flag populates unknown_option not mode

- unknown-only flag populates unknown_option not mode
   - Expected: ide_launch_unknown_only() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown-only flag populates unknown_option not mode")
expect(ide_launch_unknown_only()).to_equal(true)
```

</details>

#### launch sanity tui mode is non-empty

- launch sanity tui mode is non-empty
   - Expected: sanity.tui_mode.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("launch sanity tui mode is non-empty")
val sanity = ide_launch_sanity()
expect(sanity.tui_mode.len() > 0).to_equal(true)
```

</details>

#### launch sanity bad mode populates unknown_option

- launch sanity bad mode populates unknown_option
   - Expected: sanity.unknown_option.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("launch sanity bad mode populates unknown_option")
val sanity = ide_launch_sanity()
expect(sanity.unknown_option.len() > 0).to_equal(true)
```

</details>

#### launch sanity file_count is non-negative

- launch sanity file_count is non-negative
   - Expected: sanity.file_count >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("launch sanity file_count is non-negative")
val sanity = ide_launch_sanity()
expect(sanity.file_count >= 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ide/ide_launch_harden_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering launch_sanity: empty argv and unknown option handling.
- launch_sanity: empty argv and unknown option handling

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

- Canonical SPipe generation for source `cdec2c92693d3fcbd94c06a796c00e163c4d06bd8427657eb77eedd9e3b5c2d9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cdec2c92693d3fcbd94c06a796c00e163c4d06bd8427657eb77eedd9e3b5c2d9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cdec2c92693d3fcbd94c06a796c00e163c4d06bd8427657eb77eedd9e3b5c2d9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/ide/ide_launch_harden_spec.spl
mirror: doc/06_spec/01_unit/app/ide/ide_launch_harden_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/ide/ide_launch_harden_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ide/ide_launch_harden_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ide/ide_launch_harden_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty argv parse does not crash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ide/ide_launch_harden_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unknown-only flag populates unknown_option not mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ide/ide_launch_harden_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'launch sanity tui mode is non-empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
