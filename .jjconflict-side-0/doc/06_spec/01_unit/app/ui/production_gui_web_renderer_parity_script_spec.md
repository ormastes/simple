# Production Gui Web Renderer Parity Script Specification

> Tests covering production GUI web renderer parity wrapper.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Production Gui Web Renderer Parity Script Specification

## Scenarios

### production GUI web renderer parity wrapper

#### runs the Electron layout manifest fresh by default

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs the Electron layout manifest fresh by default
   - Expected: source does not contain `ELECTRON_LAYOUT_MANIFEST_RESUME=1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("runs the Electron layout manifest fresh by default")
val source = rt_file_read_text("scripts/check/check-production-gui-web-renderer-parity-evidence.shs") ?? ""

expect(source).to_contain("LAYOUT_MANIFEST_RESUME=")
expect(source).to_contain("PRODUCTION_GUI_WEB_RENDERER_PARITY_LAYOUT_MANIFEST_RESUME:-0")
expect(source).to_contain("ELECTRON_LAYOUT_MANIFEST_RESUME=\"$LAYOUT_MANIFEST_RESUME\"")
expect(source.contains("ELECTRON_LAYOUT_MANIFEST_RESUME=1")).to_equal(false)
```

</details>

#### keeps stale layout evidence reuse behind an explicit production override

- keeps stale layout evidence reuse behind an explicit production override


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps stale layout evidence reuse behind an explicit production override")
val source = rt_file_read_text("scripts/check/check-production-gui-web-renderer-parity-evidence.shs") ?? ""

expect(source).to_contain("PRODUCTION_GUI_WEB_RENDERER_PARITY_LAYOUT_MANIFEST_RESUME")
expect(source).to_contain("check-electron-simple-web-layout-manifest-evidence.shs")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/production_gui_web_renderer_parity_script_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering production GUI web renderer parity wrapper.
- production GUI web renderer parity wrapper

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `06b3097e8377454e2525c7f4c0d758bd4ae06100c8d308a1d2ebadb4f6644781`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `06b3097e8377454e2525c7f4c0d758bd4ae06100c8d308a1d2ebadb4f6644781`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `06b3097e8377454e2525c7f4c0d758bd4ae06100c8d308a1d2ebadb4f6644781`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/ui/production_gui_web_renderer_parity_script_spec.spl
mirror: doc/06_spec/01_unit/app/ui/production_gui_web_renderer_parity_script_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/app/ui/production_gui_web_renderer_parity_script_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ui/production_gui_web_renderer_parity_script_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ui/production_gui_web_renderer_parity_script_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/ui/production_gui_web_renderer_parity_script_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs the Electron layout manifest fresh by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui/production_gui_web_renderer_parity_script_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps stale layout evidence reuse behind an explicit production override' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
