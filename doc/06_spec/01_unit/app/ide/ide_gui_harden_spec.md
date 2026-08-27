# Ide Gui Harden Specification

> Tests covering gui_sanity: headless degradation — bounds and config checks.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ide Gui Harden Specification

## Scenarios

### gui_sanity: headless degradation — bounds and config checks

#### gui backend config has positive width (sane default even in headless)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- gui backend config has positive width (sane default even in headless)
   - Expected: ide_gui_bounds_valid() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gui backend config has positive width (sane default even in headless)")
expect(ide_gui_bounds_valid()).to_equal(true)
```

</details>

#### ide_gui_sanity returns a result without crashing

- ide_gui_sanity returns a result without crashing
   - Expected: sanity.theme.len() >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ide_gui_sanity returns a result without crashing")
val sanity = ide_gui_sanity()
expect(sanity.theme.len() >= 0).to_equal(true)
```

</details>

#### gui config width is positive

- gui config width is positive
   - Expected: sanity.width > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gui config width is positive")
val sanity = ide_gui_sanity()
expect(sanity.width > 0).to_equal(true)
```

</details>

#### gui config height is positive

- gui config height is positive
   - Expected: sanity.height > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gui config height is positive")
val sanity = ide_gui_sanity()
expect(sanity.height > 0).to_equal(true)
```

</details>

#### gui sanity has_backend_config is true

- gui sanity has_backend_config is true
   - Expected: sanity.has_backend_config is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gui sanity has_backend_config is true")
val sanity = ide_gui_sanity()
expect(sanity.has_backend_config).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ide/ide_gui_harden_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gui_sanity: headless degradation — bounds and config checks.
- gui_sanity: headless degradation — bounds and config checks

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

- Canonical SPipe generation for source `ecbc3684c1605b356a2c3b4b7112dff6010d1aff6b4603725a131f2026c7d2da`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ecbc3684c1605b356a2c3b4b7112dff6010d1aff6b4603725a131f2026c7d2da`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ecbc3684c1605b356a2c3b4b7112dff6010d1aff6b4603725a131f2026c7d2da`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/ide/ide_gui_harden_spec.spl
mirror: doc/06_spec/01_unit/app/ide/ide_gui_harden_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/ide/ide_gui_harden_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ide/ide_gui_harden_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ide/ide_gui_harden_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gui backend config has positive width (sane default even in headless)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ide/ide_gui_harden_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ide_gui_sanity returns a result without crashing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ide/ide_gui_harden_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gui config width is positive' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
