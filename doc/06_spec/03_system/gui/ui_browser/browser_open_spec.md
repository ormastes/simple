# Browser Open Specification

> Tests covering Browser Engine portable snapshot smoke, Browser Engine portable GUI gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Open Specification

## Scenarios

### Browser Engine portable snapshot smoke

#### records snapshot path and format

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records snapshot path and format
   - Expected: format equals `P3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records snapshot path and format")
val snapshot = ".build/ui_browser/test_hello.ppm"
val format = "P3"
expect(snapshot).to_end_with(".ppm")
expect(format).to_equal("P3")
```

</details>

#### records default snapshot dimensions

- records default snapshot dimensions
   - Expected: width equals `1280`
   - Expected: height equals `720`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records default snapshot dimensions")
val width = 1280
val height = 720
expect(width).to_equal(1280)
expect(height).to_equal(720)
```

</details>

#### records non-background paint colors

- records non-background paint colors


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records non-background paint colors")
val panel_rgb = "45 45 45"
val text_rgb = "224 224 224"
expect(panel_rgb).to_contain("45")
expect(text_rgb).to_contain("224")
```

</details>

### Browser Engine portable GUI gate

#### keeps GUI open behavior opt-in

- keeps GUI open behavior opt-in
   - Expected: env_name equals `SIMPLE_GUI_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps GUI open behavior opt-in")
val env_name = "SIMPLE_GUI_TEST"
expect(env_name).to_equal("SIMPLE_GUI_TEST")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/ui_browser/browser_open_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Browser Engine portable snapshot smoke, Browser Engine portable GUI gate.
- Browser Engine portable snapshot smoke
- Browser Engine portable GUI gate

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `881c2c0ac626564d150c2a206c09fec232de7751c2f3d45993e79b975ad3a644`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `881c2c0ac626564d150c2a206c09fec232de7751c2f3d45993e79b975ad3a644`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `881c2c0ac626564d150c2a206c09fec232de7751c2f3d45993e79b975ad3a644`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/gui/ui_browser/browser_open_spec.spl
mirror: doc/06_spec/03_system/gui/ui_browser/browser_open_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/ui_browser/browser_open_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/ui_browser/browser_open_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/ui_browser/browser_open_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/ui_browser/browser_open_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records snapshot path and format' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/ui_browser/browser_open_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records default snapshot dimensions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/ui_browser/browser_open_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records non-background paint colors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
