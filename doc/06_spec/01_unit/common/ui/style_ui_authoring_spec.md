# Style Ui Authoring Specification

> Tests covering style{} typed authoring surface, ui{} widget style bindings, style{} browser compatibility CSS.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Style Ui Authoring Specification

## Scenarios

### style{} typed authoring surface

#### defines typed tokens and component rules

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines typed tokens and component rules
   - Expected: ui_style_token_value(styles, "ui-accent") equals `#3366ff`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines typed tokens and component rules")
var styles = ui_style_surface("docs")
styles = ui_style_add_token(styles, ui_color_token("ui-accent", "#3366ff"))
styles = ui_style_add_token(styles, ui_length_token("space-md", "16px"))
styles = ui_style_add_token(styles, ui_text_token("font-body", "Inter"))
styles = ui_style_add_rule(styles, ui_component_layout_rule("button", "primary_button", "8px 12px", "1.4", "flex", "row", "", "8px"))

val css = ui_style_to_css(styles)

expect(ui_style_token_value(styles, "ui-accent")).to_equal("#3366ff")
expect(css).to_contain("--space-md: 16px;")
expect(css).to_contain(".primary_button")
expect(css).to_contain("margin: 8px 12px;")
expect(css).to_contain("line-height: 1.4;")
expect(css).to_contain("display: flex;")
expect(css).to_contain("flex-direction: row;")
expect(css).to_contain("gap: 8px;")
```

</details>

#### exports CSS into the existing SimpleTheme token resolver

- exports CSS into the existing SimpleTheme token resolver
   - Expected: theme.resolve_token("ui-accent") equals `#3366ff`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports CSS into the existing SimpleTheme token resolver")
var styles = ui_style_surface("docs")
styles = ui_style_add_token(styles, ui_color_token("ui-accent", "#3366ff"))

val theme = ui_style_to_theme(styles)

expect(theme.resolve_token("ui-accent")).to_equal("#3366ff")
```

</details>

### ui{} widget style bindings

#### binds widgets to typed style references

- binds widgets to typed style references
   - Expected: ui_surface_all_bindings_valid(styles, ui) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds widgets to typed style references")
var styles = ui_style_surface("docs")
styles = ui_style_add_rule(styles, ui_component_layout_rule("section", "content_grid", "0", "1.5", "grid", "", "1fr 2fr", "12px"))

var ui = ui_surface("article")
val binding = ui_widget_binding("main_grid", "Panel", "content_grid")
ui = ui_surface_add_widget(ui, binding)

expect(ui_surface_all_bindings_valid(styles, ui)).to_equal(true)
expect(ui_surface_to_dom_attrs(binding)).to_contain("data-ui-style=\"content_grid\"")
expect(ui_surface_to_dom_attrs(binding)).to_contain("class=\"content_grid\"")
```

</details>

#### rejects unknown style references

- rejects unknown style references
   - Expected: ui_surface_all_bindings_valid(styles, ui) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unknown style references")
var styles = ui_style_surface("docs")
styles = ui_style_add_rule(styles, ui_component_layout_rule("button", "primary_button", "4px", "1.2", "flex", "row", "", "4px"))

var ui = ui_surface("article")
ui = ui_surface_add_widget(ui, ui_widget_binding("missing", "Button", "danger_button"))

expect(ui_surface_all_bindings_valid(styles, ui)).to_equal(false)
```

</details>

### style{} browser compatibility CSS

#### covers margin, line-height, flex, and grid output selected by design

- covers margin, line-height, flex, and grid output selected by design


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers margin, line-height, flex, and grid output selected by design")
var styles = ui_style_surface("compat")
styles = ui_style_add_rule(styles, ui_component_layout_rule("toolbar", "toolbar_row", "4px 8px", "1.25", "flex", "row", "", "6px"))
styles = ui_style_add_rule(styles, ui_component_layout_rule("content", "content_grid", "0", "1.5", "grid", "", "minmax(0, 1fr) 320px", "16px"))

val css = ui_style_to_css(styles)

expect(css).to_contain("margin: 4px 8px;")
expect(css).to_contain("line-height: 1.25;")
expect(css).to_contain("display: flex;")
expect(css).to_contain("display: grid;")
expect(css).to_contain("grid-template-columns: minmax(0, 1fr) 320px;")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/ui/style_ui_authoring_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering style{} typed authoring surface, ui{} widget style bindings, style{} browser compatibility CSS.
- style{} typed authoring surface
- ui{} widget style bindings
- style{} browser compatibility CSS

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

- Canonical SPipe generation for source `68bddfa1dbeecee7e9e2663bca71a9e831e7666e99b6e866e2e8013656adedaa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `68bddfa1dbeecee7e9e2663bca71a9e831e7666e99b6e866e2e8013656adedaa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `68bddfa1dbeecee7e9e2663bca71a9e831e7666e99b6e866e2e8013656adedaa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/common/ui/style_ui_authoring_spec.spl
mirror: doc/06_spec/01_unit/common/ui/style_ui_authoring_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/common/ui/style_ui_authoring_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/common/ui/style_ui_authoring_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/common/ui/style_ui_authoring_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines typed tokens and component rules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/ui/style_ui_authoring_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports CSS into the existing SimpleTheme token resolver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/ui/style_ui_authoring_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds widgets to typed style references' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
