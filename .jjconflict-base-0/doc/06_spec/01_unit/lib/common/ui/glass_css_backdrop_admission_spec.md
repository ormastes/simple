# Glass Css Backdrop Admission Specification

> Tests covering glass CSS backdrop declarations are admissible by the WM material gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Glass Css Backdrop Admission Specification

## Scenarios

### glass CSS backdrop declarations are admissible by the WM material gate

#### admits the .widget-panel backdrop declaration used by the WM content wrapper

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- admits the .widget-panel backdrop declaration used by the WM content wrapper
   - Expected: admission.admitted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits the .widget-panel backdrop declaration used by the WM content wrapper")
val css = glass_widgets_base_css()
val raw = backdrop_value_for(css, ".widget-panel {")
expect(raw).to_not_equal("")
val admission = simple_web_backdrop_admission(raw)
expect(admission.admitted).to_equal(true)
```

</details>

#### realizes a nonzero blur and saturation for .widget-panel

- realizes a nonzero blur and saturation for .widget-panel
   - Expected: admission.realized_blur_px > 0 is true
   - Expected: admission.realized_saturation_milli > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("realizes a nonzero blur and saturation for .widget-panel")
val css = glass_widgets_base_css()
val admission = simple_web_backdrop_admission(
    backdrop_value_for(css, ".widget-panel {"))
expect(admission.realized_blur_px > 0).to_equal(true)
expect(admission.realized_saturation_milli > 0).to_equal(true)
```

</details>

#### admits every wrapper-applied surface class backdrop declaration

- admits every wrapper-applied surface class backdrop declaration
   - Expected: simple_web_backdrop_admission(raw).admitted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits every wrapper-applied surface class backdrop declaration")
val css = glass_widgets_base_css()
val wrapper_selectors = [
    ".widget-panel {",
    ".widget-panel"
]
for selector in wrapper_selectors:
    val raw = backdrop_value_for(css, selector)
    if raw.len() > 0:
        expect(simple_web_backdrop_admission(raw).admitted).to_equal(true)
```

</details>

#### keeps -webkit-backdrop-filter byte-identical to backdrop-filter for .widget-panel

- keeps -webkit-backdrop-filter byte-identical to backdrop-filter for .widget-panel
   - Expected: prop >= 0 is true
   - Expected: prefixed equals `standard`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps -webkit-backdrop-filter byte-identical to backdrop-filter for .widget-panel")
val css = glass_widgets_base_css()
val standard = backdrop_value_for(css, ".widget-panel {")
val at = css.find(".widget-panel {")
val rest = css.substring(at, css.len())
val prop = rest.find("-webkit-backdrop-filter:")
expect(prop >= 0).to_equal(true)
val after = rest.substring(prop + 24, rest.len())
val semi = after.find(";")
val prefixed = after.substring(0, semi).trim()
expect(prefixed).to_equal(standard)
```

</details>

#### documents the admission grammar the CSS side must satisfy

- documents the admission grammar the CSS side must satisfy
   - Expected: simple_web_backdrop_admission("blur(16px) saturate(130%)").admitted is true
   - Expected: simple_web_backdrop_admission("blur(16px)").admitted is true
   - Expected: simple_web_backdrop_admission("blur(var(--glass-blur-surface))").admitted is false
   - Expected: simple_web_backdrop_admission("blur(16px) saturate(130%) brightness(110%)").admitted is false
   - Expected: simple_web_backdrop_admission("").admitted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents the admission grammar the CSS side must satisfy")
expect(simple_web_backdrop_admission("blur(16px) saturate(130%)").admitted).to_equal(true)
expect(simple_web_backdrop_admission("blur(16px)").admitted).to_equal(true)
expect(simple_web_backdrop_admission("blur(var(--glass-blur-surface))").admitted).to_equal(false)
expect(simple_web_backdrop_admission("blur(16px) saturate(130%) brightness(110%)").admitted).to_equal(false)
expect(simple_web_backdrop_admission("").admitted).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/glass_css_backdrop_admission_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering glass CSS backdrop declarations are admissible by the WM material gate.
- glass CSS backdrop declarations are admissible by the WM material gate

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

- Canonical SPipe generation for source `c1e56737c415c4ac6eb456aac4abebb0c535949bd4cbedff1fb0df289ef1318f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c1e56737c415c4ac6eb456aac4abebb0c535949bd4cbedff1fb0df289ef1318f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c1e56737c415c4ac6eb456aac4abebb0c535949bd4cbedff1fb0df289ef1318f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/glass_css_backdrop_admission_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/glass_css_backdrop_admission_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/glass_css_backdrop_admission_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/glass_css_backdrop_admission_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/glass_css_backdrop_admission_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits the .widget-panel backdrop declaration used by the WM content wrapper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/glass_css_backdrop_admission_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'realizes a nonzero blur and saturation for .widget-panel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/glass_css_backdrop_admission_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits every wrapper-applied surface class backdrop declaration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
