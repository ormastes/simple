# Demo Render Specification

> Tests covering Demo UI Rendering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Demo Render Specification

## Scenarios

### Demo UI Rendering

#### renders demo_basics.ui.sdn

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders demo_basics.ui.sdn


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders demo_basics.ui.sdn")
val result = parse_ui_file("examples/06_io/ui/demo_basics.ui.sdn")
match result:
    case Ok(html):
        expect html to_contain "Basic Widgets Demo"
        expect html to_contain "Hello, Simple UI!"
        expect html to_contain "Welcome"
        expect html to_contain "Text Variants"
    case Err(msg):
        expect false to_equal true
```

</details>

#### renders demo_controls.ui.sdn

- renders demo_controls.ui.sdn


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders demo_controls.ui.sdn")
val result = parse_ui_file("examples/06_io/ui/demo_controls.ui.sdn")
match result:
    case Ok(html):
        expect html to_contain "Interactive Controls Demo"
        expect html to_contain "Buttons"
        expect html to_contain "Checkboxes"
        expect html to_contain "Dropdown"
    case Err(msg):
        expect false to_equal true
```

</details>

#### renders demo_forms.ui.sdn

- renders demo_forms.ui.sdn


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders demo_forms.ui.sdn")
val result = parse_ui_file("examples/06_io/ui/demo_forms.ui.sdn")
match result:
    case Ok(html):
        expect html to_contain "Form Inputs Demo"
        expect html to_contain "Text Inputs"
        expect html to_contain "Validation States"
        expect html to_contain "Text Areas"
    case Err(msg):
        expect false to_equal true
```

</details>

#### renders demo_collections.ui.sdn

- renders demo_collections.ui.sdn


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders demo_collections.ui.sdn")
val result = parse_ui_file("examples/06_io/ui/demo_collections.ui.sdn")
match result:
    case Ok(html):
        expect html to_contain "Collections Demo"
        expect html to_contain "List"
        expect html to_contain "Table"
        expect html to_contain "File Browser"
    case Err(msg):
        expect false to_equal true
```

</details>

#### renders demo_navigation.ui.sdn

- renders demo_navigation.ui.sdn


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders demo_navigation.ui.sdn")
val result = parse_ui_file("examples/06_io/ui/demo_navigation.ui.sdn")
match result:
    case Ok(html):
        expect html to_contain "Navigation Demo"
        expect html to_contain "menubar"
        expect html to_contain "Dashboard"
        expect html to_contain "Quick Stats"
    case Err(msg):
        expect false to_equal true
```

</details>

#### renders demo_display.ui.sdn

- renders demo_display.ui.sdn


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders demo_display.ui.sdn")
val result = parse_ui_file("examples/06_io/ui/demo_display.ui.sdn")
match result:
    case Ok(html):
        expect html to_contain "Display Widgets Demo"
        expect html to_contain "progress"
        expect html to_contain "Progress Bars"
        expect html to_contain "Tooltip Example"
    case Err(msg):
        expect false to_equal true
```

</details>

#### renders demo_layouts.ui.sdn

- renders demo_layouts.ui.sdn


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders demo_layouts.ui.sdn")
val result = parse_ui_file("examples/06_io/ui/demo_layouts.ui.sdn")
match result:
    case Ok(html):
        expect html to_contain "Layout Demo"
        expect html to_contain "hbox"
        expect html to_contain "Grid Layout"
        expect html to_contain "Deep Nesting"
    case Err(msg):
        expect false to_equal true
```

</details>

#### renders demo_overlays.ui.sdn

- renders demo_overlays.ui.sdn


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders demo_overlays.ui.sdn")
val result = parse_ui_file("examples/06_io/ui/demo_overlays.ui.sdn")
match result:
    case Ok(html):
        expect html to_contain "Overlays Demo"
        expect html to_contain "Scroll Container"
        expect html to_contain "Log entry 1"
        expect html to_contain "Confirm Action"
    case Err(msg):
        expect false to_equal true
```

</details>

#### renders demo_themes.ui.sdn

- renders demo_themes.ui.sdn


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders demo_themes.ui.sdn")
val result = parse_ui_file("examples/06_io/ui/demo_themes.ui.sdn")
match result:
    case Ok(html):
        expect html to_contain "Theme Showcase"
        expect html to_contain "Navigation"
        expect html to_contain "Widget Gallery"
    case Err(msg):
        expect false to_equal true
```

</details>

#### renders demo_kitchen_sink.ui.sdn

- renders demo_kitchen_sink.ui.sdn


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders demo_kitchen_sink.ui.sdn")
val result = parse_ui_file("examples/06_io/ui/demo_kitchen_sink.ui.sdn")
match result:
    case Ok(html):
        expect html to_contain "Kitchen Sink"
        expect html to_contain "Sidebar"
        expect html to_contain "Main Content"
        expect html to_contain "Kitchen Sink Demo"
    case Err(msg):
        expect false to_equal true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/ui/demo_render_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Demo UI Rendering.
- Demo UI Rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `5e015c72443c7fca1f113f69e22a8fc73d7c93411e77e97026b53900bf1ff7d0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5e015c72443c7fca1f113f69e22a8fc73d7c93411e77e97026b53900bf1ff7d0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5e015c72443c7fca1f113f69e22a8fc73d7c93411e77e97026b53900bf1ff7d0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/ui/demo_render_spec.spl
mirror: doc/06_spec/03_system/gui/ui/demo_render_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/ui/demo_render_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/ui/demo_render_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/ui/demo_render_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders demo_basics.ui.sdn' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/ui/demo_render_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders demo_controls.ui.sdn' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/ui/demo_render_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders demo_forms.ui.sdn' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
