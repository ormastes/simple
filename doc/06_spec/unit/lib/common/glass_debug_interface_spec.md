# Glass Debug Interface Specification

> AC-5: CLI-based GUI debug interface exists (inspect widget tree, theme tokens, CSS output) via MCP or CLI subcommand.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Glass Debug Interface Specification

AC-5: CLI-based GUI debug interface exists (inspect widget tree, theme tokens, CSS output) via MCP or CLI subcommand.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GUI-THEME-SHARING |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | doc/05_design/stitch_design_system.md |
| Source | `test/unit/lib/common/glass_debug_interface_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

AC-5: CLI-based GUI debug interface exists (inspect widget tree, theme
tokens, CSS output) via MCP or CLI subcommand.

Verifies that:
- debug_theme_tokens(theme_name) returns non-empty text for valid themes
- debug_css_dump(theme_name) returns non-empty text for valid themes
- debug_widget_tree(theme_name) returns non-empty text for valid themes
- All debug functions return meaningful content (not just whitespace)
- Debug functions handle unknown themes gracefully
- Output contains expected structural elements

## Key Concepts

| Concept | Description |
|---------|-------------|
| debug_theme_tokens | Pure function returning all token values as formatted text |
| debug_css_dump | Pure function returning full CSS output for a theme |
| debug_widget_tree | Pure function returning widget tree with theme assignments |
| Pure functions | No side effects, usable from both MCP tools and CLI |

## Scenarios

### debug_theme_tokens

#### returns non-empty text for glass_dark

- returns non-empty text for glass_dark


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty text for glass_dark")
val output = debug_theme_tokens("glass_dark")
expect(output.len()).to_be_greater_than(0)
```

</details>

#### returns non-empty text for glass_light

- returns non-empty text for glass_light


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty text for glass_light")
val output = debug_theme_tokens("glass_light")
expect(output.len()).to_be_greater_than(0)
```

</details>

#### returns non-empty text for glass_obsidian_dark

- returns non-empty text for glass_obsidian_dark


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty text for glass_obsidian_dark")
val output = debug_theme_tokens("glass_obsidian_dark")
expect(output.len()).to_be_greater_than(0)
```

</details>

#### contains surface_primary label

- contains surface_primary label


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains surface_primary label")
val output = debug_theme_tokens("glass_dark")
expect(output).to_contain("surface_primary")
```

</details>

#### contains text_primary label

- contains text_primary label


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains text_primary label")
val output = debug_theme_tokens("glass_dark")
expect(output).to_contain("text_primary")
```

</details>

#### contains accent label

- contains accent label


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains accent label")
val output = debug_theme_tokens("glass_dark")
expect(output).to_contain("accent")
```

</details>

#### contains blur token info

- contains blur token info


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains blur token info")
val output = debug_theme_tokens("glass_dark")
expect(output).to_contain("blur")
```

</details>

#### obsidian output contains Obsidian-specific value

- obsidian output contains Obsidian-specific value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("obsidian output contains Obsidian-specific value")
val output = debug_theme_tokens("glass_obsidian_dark")
expect(output).to_contain("#E3E0F3")
```

</details>

#### dark output contains dark-specific value

- dark output contains dark-specific value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dark output contains dark-specific value")
val output = debug_theme_tokens("glass_dark")
expect(output).to_contain("#F5F5F7")
```

</details>

### debug_css_dump

#### returns non-empty text for glass_dark

- returns non-empty text for glass_dark


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty text for glass_dark")
val output = debug_css_dump("glass_dark")
expect(output.len()).to_be_greater_than(0)
```

</details>

#### returns non-empty text for glass_light

- returns non-empty text for glass_light


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty text for glass_light")
val output = debug_css_dump("glass_light")
expect(output.len()).to_be_greater_than(0)
```

</details>

#### returns non-empty text for glass_obsidian_dark

- returns non-empty text for glass_obsidian_dark


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty text for glass_obsidian_dark")
val output = debug_css_dump("glass_obsidian_dark")
expect(output.len()).to_be_greater_than(0)
```

</details>

#### contains :root block

- contains :root block


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains :root block")
val output = debug_css_dump("glass_dark")
expect(output).to_contain(":root")
```

</details>

#### contains CSS custom properties

- contains CSS custom properties


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains CSS custom properties")
val output = debug_css_dump("glass_dark")
expect(output).to_contain("--glass-")
```

</details>

#### contains component CSS

- contains component CSS


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains component CSS")
val output = debug_css_dump("glass_dark")
expect(output).to_contain(".widget-panel")
```

</details>

### debug_widget_tree

#### returns non-empty text for glass_dark

- returns non-empty text for glass_dark


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty text for glass_dark")
val output = debug_widget_tree("glass_dark")
expect(output.len()).to_be_greater_than(0)
```

</details>

#### returns non-empty text for glass_obsidian_dark

- returns non-empty text for glass_obsidian_dark


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty text for glass_obsidian_dark")
val output = debug_widget_tree("glass_obsidian_dark")
expect(output.len()).to_be_greater_than(0)
```

</details>

#### contains widget class names

- contains widget class names


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains widget class names")
val output = debug_widget_tree("glass_dark")
expect(output).to_contain("widget")
```

</details>

#### contains CSS variable references

- contains CSS variable references


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains CSS variable references")
val output = debug_widget_tree("glass_dark")
expect(output).to_contain("--glass-")
```

</details>

#### contains panel widget info

- contains panel widget info


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains panel widget info")
val output = debug_widget_tree("glass_dark")
expect(output).to_contain("panel")
```

</details>

#### contains window widget info

- contains window widget info


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains window widget info")
val output = debug_widget_tree("glass_dark")
expect(output).to_contain("window")
```

</details>

### Debug functions with unknown themes

#### debug_theme_tokens handles unknown theme

- debug_theme_tokens handles unknown theme


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug_theme_tokens handles unknown theme")
val output = debug_theme_tokens("nonexistent")
# Should not crash -- either empty or error message
expect(output.len()).to_be_greater_than(-1)
```

</details>

#### debug_css_dump handles unknown theme

- debug_css_dump handles unknown theme


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug_css_dump handles unknown theme")
val output = debug_css_dump("nonexistent")
expect(output.len()).to_be_greater_than(-1)
```

</details>

#### debug_widget_tree handles unknown theme

- debug_widget_tree handles unknown theme


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug_widget_tree handles unknown theme")
val output = debug_widget_tree("nonexistent")
expect(output.len()).to_be_greater_than(-1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** `doc/05_design/stitch_design_system.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1c0e0e710c46235ba64721d55b9c5d611bc78a45b7372d63a2a95074ec6340a0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1c0e0e710c46235ba64721d55b9c5d611bc78a45b7372d63a2a95074ec6340a0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1c0e0e710c46235ba64721d55b9c5d611bc78a45b7372d63a2a95074ec6340a0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/glass_debug_interface_spec.spl
mirror: doc/06_spec/unit/lib/common/glass_debug_interface_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/glass_debug_interface_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/glass_debug_interface_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/glass_debug_interface_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns non-empty text for glass_dark' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/glass_debug_interface_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns non-empty text for glass_light' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/glass_debug_interface_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns non-empty text for glass_obsidian_dark' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
