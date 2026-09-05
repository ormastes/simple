# Tui Theme Specification

> Tests covering get_theme_color, dark theme, dark vs light theme differences, all widget roles return non-empty, AnsiTheme.from_theme, 256-color and RGB escape helpers, Screen.put_bg, theme switching changes output.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tui Theme Specification

## Scenarios

### get_theme_color

### dark theme

#### returns non-empty string for border role

- returns non-empty string for border role


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty string for border role")
val color = get_theme_color("dark", "border")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for border_focused role

- returns non-empty string for border_focused role


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty string for border_focused role")
val color = get_theme_color("dark", "border_focused")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for button role

- returns non-empty string for button role


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty string for button role")
val color = get_theme_color("dark", "button")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for button_focused role

- returns non-empty string for button_focused role


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty string for button_focused role")
val color = get_theme_color("dark", "button_focused")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for checkbox role

- returns non-empty string for checkbox role


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty string for checkbox role")
val color = get_theme_color("dark", "checkbox")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for checkbox_checked role

- returns non-empty string for checkbox_checked role


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty string for checkbox_checked role")
val color = get_theme_color("dark", "checkbox_checked")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for input role

- returns non-empty string for input role


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty string for input role")
val color = get_theme_color("dark", "input")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for input_focused role

- returns non-empty string for input_focused role


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty string for input_focused role")
val color = get_theme_color("dark", "input_focused")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for progress_fill role

- returns non-empty string for progress_fill role


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty string for progress_fill role")
val color = get_theme_color("dark", "progress_fill")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for progress_empty role

- returns non-empty string for progress_empty role


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty string for progress_empty role")
val color = get_theme_color("dark", "progress_empty")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for tab_active role

- returns non-empty string for tab_active role


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty string for tab_active role")
val color = get_theme_color("dark", "tab_active")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for tab_inactive role

- returns non-empty string for tab_inactive role


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty string for tab_inactive role")
val color = get_theme_color("dark", "tab_inactive")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for list_selected role

- returns non-empty string for list_selected role


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty string for list_selected role")
val color = get_theme_color("dark", "list_selected")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for list_item role

- returns non-empty string for list_item role


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty string for list_item role")
val color = get_theme_color("dark", "list_item")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for dialog_border role

- returns non-empty string for dialog_border role


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty string for dialog_border role")
val color = get_theme_color("dark", "dialog_border")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for disabled role

- returns non-empty string for disabled role


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty string for disabled role")
val color = get_theme_color("dark", "disabled")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for error_fg role

- returns non-empty string for error_fg role


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty string for error_fg role")
val color = get_theme_color("dark", "error_fg")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for readonly role

- returns non-empty string for readonly role


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns non-empty string for readonly role")
val color = get_theme_color("dark", "readonly")
expect color.len() > 0 to_equal(true)
```

</details>

### dark vs light theme differences

#### border_focused differs between dark and light

- border_focused differs between dark and light


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("border_focused differs between dark and light")
val dark_color = get_theme_color("dark", "border_focused")
val light_color = get_theme_color("light", "border_focused")
expect (dark_color != light_color) to_equal(true)
```

</details>

#### button differs between dark and light

- button differs between dark and light


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("button differs between dark and light")
val dark_color = get_theme_color("dark", "button")
val light_color = get_theme_color("light", "button")
expect (dark_color != light_color) to_equal(true)
```

</details>

#### list_selected differs between dark and light

- list_selected differs between dark and light


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("list_selected differs between dark and light")
val dark_color = get_theme_color("dark", "list_selected")
val light_color = get_theme_color("light", "list_selected")
expect (dark_color != light_color) to_equal(true)
```

</details>

#### checkbox_checked differs between dark and light

- checkbox_checked differs between dark and light


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checkbox_checked differs between dark and light")
val dark_color = get_theme_color("dark", "checkbox_checked")
val light_color = get_theme_color("light", "checkbox_checked")
expect (dark_color != light_color) to_equal(true)
```

</details>

### all widget roles return non-empty

#### covers all defined roles for dark theme

- covers all defined roles for dark theme


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers all defined roles for dark theme")
val roles = ["border", "border_focused", "title", "text", "text_dim",
    "accent", "button", "button_focused", "checkbox", "checkbox_checked",
    "input", "input_focused", "progress_fill", "progress_empty",
    "tab_active", "tab_inactive", "list_selected", "list_item",
    "dialog_border", "disabled", "error_fg", "readonly"]
var all_non_empty = true
for role in roles:
    val c = get_theme_color("dark", role)
    if c.len() == 0:
        all_non_empty = false
expect all_non_empty to_equal(true)
```

</details>

#### covers all defined roles for light theme

- covers all defined roles for light theme


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers all defined roles for light theme")
val roles = ["border", "border_focused", "title", "text", "text_dim",
    "accent", "button", "button_focused", "checkbox", "checkbox_checked",
    "input", "input_focused", "progress_fill", "progress_empty",
    "tab_active", "tab_inactive", "list_selected", "list_item",
    "dialog_border", "disabled", "error_fg", "readonly"]
var all_non_empty = true
for role in roles:
    val c = get_theme_color("light", role)
    if c.len() == 0:
        all_non_empty = false
expect all_non_empty to_equal(true)
```

</details>

### AnsiTheme.from_theme

#### populates all general fields from dark theme

- populates all general fields from dark theme


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("populates all general fields from dark theme")
val theme = UITheme.dark()
val ansi = AnsiTheme.from_theme(theme)
expect ansi.border.len() > 0 to_equal(true)
expect ansi.accent.len() > 0 to_equal(true)
expect ansi.error.len() > 0 to_equal(true)
expect ansi.warning.len() > 0 to_equal(true)
expect ansi.success.len() > 0 to_equal(true)
expect ansi.dim.len() > 0 to_equal(true)
expect ansi.bold.len() > 0 to_equal(true)
expect ansi.reset.len() > 0 to_equal(true)
```

</details>

#### populates per-widget fields from dark theme

- populates per-widget fields from dark theme


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("populates per-widget fields from dark theme")
val theme = UITheme.dark()
val ansi = AnsiTheme.from_theme(theme)
expect ansi.button.len() > 0 to_equal(true)
expect ansi.button_focused.len() > 0 to_equal(true)
expect ansi.checkbox.len() > 0 to_equal(true)
expect ansi.checkbox_checked.len() > 0 to_equal(true)
expect ansi.input.len() > 0 to_equal(true)
expect ansi.input_focused.len() > 0 to_equal(true)
expect ansi.progress_fill.len() > 0 to_equal(true)
expect ansi.progress_empty.len() > 0 to_equal(true)
expect ansi.tab_active.len() > 0 to_equal(true)
expect ansi.tab_inactive.len() > 0 to_equal(true)
expect ansi.list_selected.len() > 0 to_equal(true)
expect ansi.list_item.len() > 0 to_equal(true)
expect ansi.dialog_border.len() > 0 to_equal(true)
expect ansi.disabled_fg.len() > 0 to_equal(true)
expect ansi.error_fg.len() > 0 to_equal(true)
expect ansi.readonly_fg.len() > 0 to_equal(true)
```

</details>

#### populates all fields from light theme

- populates all fields from light theme


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("populates all fields from light theme")
val theme = UITheme.light()
val ansi = AnsiTheme.from_theme(theme)
expect ansi.border.len() > 0 to_equal(true)
expect ansi.button.len() > 0 to_equal(true)
expect ansi.checkbox_checked.len() > 0 to_equal(true)
expect ansi.list_selected.len() > 0 to_equal(true)
expect ansi.dialog_border.len() > 0 to_equal(true)
```

</details>

#### produces different accent for dark vs light

- produces different accent for dark vs light


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces different accent for dark vs light")
val dark_ansi = AnsiTheme.from_theme(UITheme.dark())
val light_ansi = AnsiTheme.from_theme(UITheme.light())
expect (dark_ansi.accent != light_ansi.accent) to_equal(true)
```

</details>

#### produces different button for dark vs light

- produces different button for dark vs light


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces different button for dark vs light")
val dark_ansi = AnsiTheme.from_theme(UITheme.dark())
val light_ansi = AnsiTheme.from_theme(UITheme.light())
expect (dark_ansi.button != light_ansi.button) to_equal(true)
```

</details>

### 256-color and RGB escape helpers

#### ansi_fg_256 produces correct escape sequence

- ansi_fg_256 produces correct escape sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ansi_fg_256 produces correct escape sequence")
val result = ansi_fg_256(196)
expect result to_contain("38;5;196")
```

</details>

#### ansi_bg_256 produces correct escape sequence

- ansi_bg_256 produces correct escape sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ansi_bg_256 produces correct escape sequence")
val result = ansi_bg_256(21)
expect result to_contain("48;5;21")
```

</details>

#### ansi_fg_256 with color 0 works

- ansi_fg_256 with color 0 works


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ansi_fg_256 with color 0 works")
val result = ansi_fg_256(0)
expect result to_contain("38;5;0")
```

</details>

#### ansi_fg_256 with color 255 works

- ansi_fg_256 with color 255 works


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ansi_fg_256 with color 255 works")
val result = ansi_fg_256(255)
expect result to_contain("38;5;255")
```

</details>

#### ansi_bg_256 with color 232 works

- ansi_bg_256 with color 232 works


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ansi_bg_256 with color 232 works")
val result = ansi_bg_256(232)
expect result to_contain("48;5;232")
```

</details>

#### ansi_fg_rgb produces correct escape sequence

- ansi_fg_rgb produces correct escape sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ansi_fg_rgb produces correct escape sequence")
val result = ansi_fg_rgb(255, 128, 0)
expect result to_contain("38;2;255;128;0")
```

</details>

#### ansi_bg_rgb produces correct escape sequence

- ansi_bg_rgb produces correct escape sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ansi_bg_rgb produces correct escape sequence")
val result = ansi_bg_rgb(0, 0, 255)
expect result to_contain("48;2;0;0;255")
```

</details>

#### ansi_fg_rgb with black produces correct sequence

- ansi_fg_rgb with black produces correct sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ansi_fg_rgb with black produces correct sequence")
val result = ansi_fg_rgb(0, 0, 0)
expect result to_contain("38;2;0;0;0")
```

</details>

#### ansi_bg_rgb with white produces correct sequence

- ansi_bg_rgb with white produces correct sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ansi_bg_rgb with white produces correct sequence")
val result = ansi_bg_rgb(255, 255, 255)
expect result to_contain("48;2;255;255;255")
```

</details>

### Screen.put_bg

#### returns screen unchanged for out-of-bounds row

- returns screen unchanged for out-of-bounds row


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns screen unchanged for out-of-bounds row")
val s = Screen.new(20, 5)
val result = s.put_bg(-1, 0, 10, "\u{001b}[44m")
expect result.height to_equal(5)
```

</details>

#### returns screen unchanged for out-of-bounds col

- returns screen unchanged for out-of-bounds col


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns screen unchanged for out-of-bounds col")
val s = Screen.new(20, 5)
val result = s.put_bg(0, -1, 10, "\u{001b}[44m")
expect result.height to_equal(5)
```

</details>

### theme switching changes output

#### dark theme button color differs from light theme button color

- dark theme button color differs from light theme button color


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dark theme button color differs from light theme button color")
val dark_btn = get_theme_color("dark", "button")
val light_btn = get_theme_color("light", "button")
expect (dark_btn != light_btn) to_equal(true)
```

</details>

#### dark theme input_focused differs from light theme input_focused

- dark theme input_focused differs from light theme input_focused


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dark theme input_focused differs from light theme input_focused")
val dark_input = get_theme_color("dark", "input_focused")
val light_input = get_theme_color("light", "input_focused")
expect (dark_input != light_input) to_equal(true)
```

</details>

#### dark theme checkbox_checked differs from light theme

- dark theme checkbox_checked differs from light theme


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dark theme checkbox_checked differs from light theme")
val dark_chk = get_theme_color("dark", "checkbox_checked")
val light_chk = get_theme_color("light", "checkbox_checked")
expect (dark_chk != light_chk) to_equal(true)
```

</details>

#### dark theme dialog_border differs from light theme

- dark theme dialog_border differs from light theme


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dark theme dialog_border differs from light theme")
val dark_dlg = get_theme_color("dark", "dialog_border")
val light_dlg = get_theme_color("light", "dialog_border")
expect (dark_dlg != light_dlg) to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/tui_theme_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering get_theme_color, dark theme, dark vs light theme differences, all widget roles return non-empty, AnsiTheme.from_theme, 256-color and RGB escape helpers, Screen.put_bg, theme switching changes output.
- get_theme_color
- dark theme
- dark vs light theme differences
- all widget roles return non-empty
- AnsiTheme.from_theme
- 256-color and RGB escape helpers
- Screen.put_bg
- theme switching changes output

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
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

- Canonical SPipe generation for source `5a9bb074d592dcd25e0905d8e80a964f41336bdf924687a26550d73621166ac3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5a9bb074d592dcd25e0905d8e80a964f41336bdf924687a26550d73621166ac3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5a9bb074d592dcd25e0905d8e80a964f41336bdf924687a26550d73621166ac3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/tui_theme_spec.spl
mirror: doc/06_spec/unit/app/ui/tui_theme_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/tui_theme_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/tui_theme_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/tui_theme_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns non-empty string for border role' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/tui_theme_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns non-empty string for border_focused role' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/tui_theme_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns non-empty string for button role' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
