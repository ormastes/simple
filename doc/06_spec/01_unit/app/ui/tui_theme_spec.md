# Tui Theme Specification

> 1. expect color len

<!-- sdn-diagram:id=tui_theme_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tui_theme_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tui_theme_spec -> app
tui_theme_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tui_theme_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

1. expect color len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = get_theme_color("dark", "border")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for border_focused role

1. expect color len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = get_theme_color("dark", "border_focused")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for button role

1. expect color len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = get_theme_color("dark", "button")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for button_focused role

1. expect color len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = get_theme_color("dark", "button_focused")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for checkbox role

1. expect color len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = get_theme_color("dark", "checkbox")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for checkbox_checked role

1. expect color len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = get_theme_color("dark", "checkbox_checked")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for input role

1. expect color len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = get_theme_color("dark", "input")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for input_focused role

1. expect color len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = get_theme_color("dark", "input_focused")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for progress_fill role

1. expect color len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = get_theme_color("dark", "progress_fill")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for progress_empty role

1. expect color len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = get_theme_color("dark", "progress_empty")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for tab_active role

1. expect color len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = get_theme_color("dark", "tab_active")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for tab_inactive role

1. expect color len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = get_theme_color("dark", "tab_inactive")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for list_selected role

1. expect color len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = get_theme_color("dark", "list_selected")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for list_item role

1. expect color len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = get_theme_color("dark", "list_item")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for dialog_border role

1. expect color len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = get_theme_color("dark", "dialog_border")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for disabled role

1. expect color len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = get_theme_color("dark", "disabled")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for error_fg role

1. expect color len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = get_theme_color("dark", "error_fg")
expect color.len() > 0 to_equal(true)
```

</details>

#### returns non-empty string for readonly role

1. expect color len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = get_theme_color("dark", "readonly")
expect color.len() > 0 to_equal(true)
```

</details>

### dark vs light theme differences

#### border_focused differs between dark and light

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dark_color = get_theme_color("dark", "border_focused")
val light_color = get_theme_color("light", "border_focused")
expect (dark_color != light_color) to_equal(true)
```

</details>

#### button differs between dark and light

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dark_color = get_theme_color("dark", "button")
val light_color = get_theme_color("light", "button")
expect (dark_color != light_color) to_equal(true)
```

</details>

#### list_selected differs between dark and light

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dark_color = get_theme_color("dark", "list_selected")
val light_color = get_theme_color("light", "list_selected")
expect (dark_color != light_color) to_equal(true)
```

</details>

#### checkbox_checked differs between dark and light

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dark_color = get_theme_color("dark", "checkbox_checked")
val light_color = get_theme_color("light", "checkbox_checked")
expect (dark_color != light_color) to_equal(true)
```

</details>

### all widget roles return non-empty

#### covers all defined roles for dark theme

1. expect all non empty to equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect all non empty to equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect ansi border len
2. expect ansi accent len
3. expect ansi error len
4. expect ansi warning len
5. expect ansi success len
6. expect ansi dim len
7. expect ansi bold len
8. expect ansi reset len


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect ansi button len
2. expect ansi button focused len
3. expect ansi checkbox len
4. expect ansi checkbox checked len
5. expect ansi input len
6. expect ansi input focused len
7. expect ansi progress fill len
8. expect ansi progress empty len
9. expect ansi tab active len
10. expect ansi tab inactive len
11. expect ansi list selected len
12. expect ansi list item len
13. expect ansi dialog border len
14. expect ansi disabled fg len
15. expect ansi error fg len
16. expect ansi readonly fg len


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect ansi border len
2. expect ansi button len
3. expect ansi checkbox checked len
4. expect ansi list selected len
5. expect ansi dialog border len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dark_ansi = AnsiTheme.from_theme(UITheme.dark())
val light_ansi = AnsiTheme.from_theme(UITheme.light())
expect (dark_ansi.accent != light_ansi.accent) to_equal(true)
```

</details>

#### produces different button for dark vs light

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dark_ansi = AnsiTheme.from_theme(UITheme.dark())
val light_ansi = AnsiTheme.from_theme(UITheme.light())
expect (dark_ansi.button != light_ansi.button) to_equal(true)
```

</details>

### 256-color and RGB escape helpers

#### ansi_fg_256 produces correct escape sequence

1. expect result to contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ansi_fg_256(196)
expect result to_contain("38;5;196")
```

</details>

#### ansi_bg_256 produces correct escape sequence

1. expect result to contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ansi_bg_256(21)
expect result to_contain("48;5;21")
```

</details>

#### ansi_fg_256 with color 0 works

1. expect result to contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ansi_fg_256(0)
expect result to_contain("38;5;0")
```

</details>

#### ansi_fg_256 with color 255 works

1. expect result to contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ansi_fg_256(255)
expect result to_contain("38;5;255")
```

</details>

#### ansi_bg_256 with color 232 works

1. expect result to contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ansi_bg_256(232)
expect result to_contain("48;5;232")
```

</details>

#### ansi_fg_rgb produces correct escape sequence

1. expect result to contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ansi_fg_rgb(255, 128, 0)
expect result to_contain("38;2;255;128;0")
```

</details>

#### ansi_bg_rgb produces correct escape sequence

1. expect result to contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ansi_bg_rgb(0, 0, 255)
expect result to_contain("48;2;0;0;255")
```

</details>

#### ansi_fg_rgb with black produces correct sequence

1. expect result to contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ansi_fg_rgb(0, 0, 0)
expect result to_contain("38;2;0;0;0")
```

</details>

#### ansi_bg_rgb with white produces correct sequence

1. expect result to contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ansi_bg_rgb(255, 255, 255)
expect result to_contain("48;2;255;255;255")
```

</details>

### Screen.put_bg

#### returns screen unchanged for out-of-bounds row

1. expect result height to equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Screen.new(20, 5)
val result = s.put_bg(-1, 0, 10, "\u{001b}[44m")
expect result.height to_equal(5)
```

</details>

#### returns screen unchanged for out-of-bounds col

1. expect result height to equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Screen.new(20, 5)
val result = s.put_bg(0, -1, 10, "\u{001b}[44m")
expect result.height to_equal(5)
```

</details>

### theme switching changes output

#### dark theme button color differs from light theme button color

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dark_btn = get_theme_color("dark", "button")
val light_btn = get_theme_color("light", "button")
expect (dark_btn != light_btn) to_equal(true)
```

</details>

#### dark theme input_focused differs from light theme input_focused

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dark_input = get_theme_color("dark", "input_focused")
val light_input = get_theme_color("light", "input_focused")
expect (dark_input != light_input) to_equal(true)
```

</details>

#### dark theme checkbox_checked differs from light theme

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dark_chk = get_theme_color("dark", "checkbox_checked")
val light_chk = get_theme_color("light", "checkbox_checked")
expect (dark_chk != light_chk) to_equal(true)
```

</details>

#### dark theme dialog_border differs from light theme

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/ui/tui_theme_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
