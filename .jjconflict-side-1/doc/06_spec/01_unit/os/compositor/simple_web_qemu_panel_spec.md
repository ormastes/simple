# Simple Web Qemu Panel Specification

> Tests covering SimpleOS QEMU Simple Web panel contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Qemu Panel Specification

## Scenarios

### SimpleOS QEMU Simple Web panel contract

#### keeps the browser panel tied to Simple Web HTML

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the browser panel tied to Simple Web HTML


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps the browser panel tied to Simple Web HTML")
val html = qemu_simple_web_demo_html()
expect(html).to_contain("about:engine2d-wm")
expect(html).to_contain("Simple Web Renderer")
expect(html).to_contain("HTML -> layout -> paint -> pixels -> Engine2D")
```

</details>

#### maps HTML bands to deterministic panel colors

- maps HTML bands to deterministic panel colors
   - Expected: qemu_simple_web_panel_color_at(0, 0) equals `0xFFDCEAFBu32`
   - Expected: qemu_simple_web_panel_color_at(7, 7) equals `0xFF1D1D1Fu32`
   - Expected: qemu_simple_web_panel_color_at(4, 7) equals `0xFFDCEAFBu32`
   - Expected: qemu_simple_web_panel_color_at(0, 30) equals `0xFF182230u32`
   - Expected: qemu_simple_web_panel_color_at(0, 116) equals `0xFF1F2937u32`
   - Expected: qemu_simple_web_panel_color_at(0, 202) equals `0xFF5A7FB5u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("maps HTML bands to deterministic panel colors")
# Aqua title_focused/text_primary/desktop_bg literals (see
# common.ui.wm_chrome_theme.wm_chrome_theme_defaults); pinned here
# because the panel is freestanding and cannot thread wm_chrome_theme().
expect(qemu_simple_web_panel_color_at(0, 0)).to_equal(0xFFDCEAFBu32)
expect(qemu_simple_web_panel_color_at(7, 7)).to_equal(0xFF1D1D1Fu32)
expect(qemu_simple_web_panel_color_at(4, 7)).to_equal(0xFFDCEAFBu32)
expect(qemu_simple_web_panel_color_at(0, 30)).to_equal(0xFF182230u32)
expect(qemu_simple_web_panel_color_at(0, 116)).to_equal(0xFF1F2937u32)
expect(qemu_simple_web_panel_color_at(0, 202)).to_equal(0xFF5A7FB5u32)
```

</details>

#### emits stable pixel count and checksum evidence

- emits stable pixel count and checksum evidence
   - Expected: qemu_simple_web_panel_pixel_count(248, 118) equals `29264`
   - Expected: qemu_simple_web_panel_pixel_count(270, 114) equals `30780`
   - Expected: qemu_simple_web_panel_checksum(248, 118) equals `qemu_simple_web_panel_checksum(248, 118)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("emits stable pixel count and checksum evidence")
expect(qemu_simple_web_panel_pixel_count(248, 118)).to_equal(29264)
expect(qemu_simple_web_panel_pixel_count(270, 114)).to_equal(30780)
expect(qemu_simple_web_panel_checksum(8, 8)).to_be_greater_than(0)
expect(qemu_simple_web_panel_checksum(248, 118)).to_equal(qemu_simple_web_panel_checksum(248, 118))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/simple_web_qemu_panel_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS QEMU Simple Web panel contract.
- SimpleOS QEMU Simple Web panel contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `87703345d7f92bf439b7fa335aa67243c90e8a50022875adfe5f6a2c8bae840c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `87703345d7f92bf439b7fa335aa67243c90e8a50022875adfe5f6a2c8bae840c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `87703345d7f92bf439b7fa335aa67243c90e8a50022875adfe5f6a2c8bae840c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/os/compositor/simple_web_qemu_panel_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/simple_web_qemu_panel_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/simple_web_qemu_panel_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/simple_web_qemu_panel_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/simple_web_qemu_panel_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/compositor/simple_web_qemu_panel_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the browser panel tied to Simple Web HTML' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/simple_web_qemu_panel_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps HTML bands to deterministic panel colors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/simple_web_qemu_panel_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits stable pixel count and checksum evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
