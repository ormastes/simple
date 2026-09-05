# Widget Menu Tooltip Specification

> Tests covering menu_separator builder, menu_with_submenu builder, menubar_rich builder, TUI menubar separator rendering, HTML menubar separator rendering, Tooltip builder, TUI tooltip rendering, HTML tooltip rendering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Menu Tooltip Specification

## Scenarios

### menu_separator builder

#### creates a text widget

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates a text widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a text widget")
val sep = menu_separator("msep_kind_1")
expect sep.kind_name() to_equal "text"
```

</details>

#### has is_separator prop set to true

- has is_separator prop set to true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has is_separator prop set to true")
val sep = menu_separator("msep_prop_1")
expect sep.get_prop("is_separator") to_equal "true"
```

</details>

#### has label set to pipe character

- has label set to pipe character


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has label set to pipe character")
val sep = menu_separator("msep_label_1")
expect sep.get_prop("label") to_equal "|"
```

</details>

#### has correct id

- has correct id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct id")
val sep = menu_separator("msep_id_1")
expect sep.id to_equal "msep_id_1"
```

</details>

#### has no children

- has no children


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has no children")
val sep = menu_separator("msep_child_1")
expect sep.child_count() to_equal 0
```

</details>

### menu_with_submenu builder

#### creates a text widget

- creates a text widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a text widget")
val sub = menu_with_submenu("msub_kind_1", "Edit", [])
expect sub.kind_name() to_equal "text"
```

</details>

#### has has_submenu prop set to true

- has has_submenu prop set to true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has has_submenu prop set to true")
val sub = menu_with_submenu("msub_prop_1", "Edit", [])
expect sub.get_prop("has_submenu") to_equal "true"
```

</details>

#### has label set to given text

- has label set to given text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has label set to given text")
val sub = menu_with_submenu("msub_label_1", "Edit", [])
expect sub.get_prop("label") to_equal "Edit"
```

</details>

#### stores children as submenu items

- stores children as submenu items


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores children as submenu items")
val cut = label("msub_cut_1", "Cut")
val copy = label("msub_copy_1", "Copy")
val sub = menu_with_submenu("msub_children_1", "Edit", [cut, copy])
expect sub.child_count() to_equal 2
```

</details>

#### first child has correct label

- first child has correct label


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first child has correct label")
val cut = label("msub_cut_2", "Cut")
val copy = label("msub_copy_2", "Copy")
val sub = menu_with_submenu("msub_children_2", "Edit", [cut, copy])
val first = sub.child_at(0)
expect first.get_prop("label") to_equal "Cut"
```

</details>

#### has correct id

- has correct id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct id")
val sub = menu_with_submenu("msub_id_1", "View", [])
expect sub.id to_equal "msub_id_1"
```

</details>

### menubar_rich builder

#### creates a menubar kind widget

- creates a menubar kind widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a menubar kind widget")
val bar = menubar_rich("mrich_kind_1", [])
expect bar.kind_name() to_equal "menubar"
```

</details>

#### accepts mixed items

- accepts mixed items


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts mixed items")
val file_item = label("mrich_file_1", "File")
val sep = menu_separator("mrich_sep_1")
val edit_cut = label("mrich_edit_cut_1", "Cut")
val edit_sub = menu_with_submenu("mrich_edit_1", "Edit", [edit_cut])
val bar = menubar_rich("mrich_mixed_1", [file_item, sep, edit_sub])
expect bar.child_count() to_equal 3
```

</details>

#### first child is a normal item

- first child is a normal item


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first child is a normal item")
val file_item = label("mrich_file_2", "File")
val sep = menu_separator("mrich_sep_2")
val bar = menubar_rich("mrich_order_1", [file_item, sep])
val first = bar.child_at(0)
expect first.get_prop("label") to_equal "File"
```

</details>

#### second child is a separator

- second child is a separator


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("second child is a separator")
val file_item = label("mrich_file_3", "File")
val sep = menu_separator("mrich_sep_3")
val bar = menubar_rich("mrich_order_2", [file_item, sep])
val second = bar.child_at(1)
expect second.get_prop("is_separator") to_equal "true"
```

</details>

#### third child is a submenu

- third child is a submenu


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("third child is a submenu")
val file_item = label("mrich_file_4", "File")
val sep = menu_separator("mrich_sep_4")
val edit_sub = menu_with_submenu("mrich_edit_4", "Edit", [])
val bar = menubar_rich("mrich_order_3", [file_item, sep, edit_sub])
val third = bar.child_at(2)
expect third.get_prop("has_submenu") to_equal "true"
```

</details>

### TUI menubar separator rendering

#### separator shows pipe character in output

- separator shows pipe character in output


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("separator shows pipe character in output")
val file_item = label("tui_sep_file_1", "File")
val sep = menu_separator("tui_sep_sep_1")
val view_item = label("tui_sep_view_1", "View")
val bar = menubar_rich("tui_sep_bar_1", [file_item, sep, view_item])
val rect = WidgetRect(id: "tui_sep_bar_1", x: 0, y: 0, w: 80, h: 1)
var screen = Screen.new(80, 1)
screen = render_tui_menubar(screen, bar, rect)
val row_text = screen.buffer[0]
expect row_text to_contain "|"
```

</details>

#### submenu label appears in output

- submenu label appears in output


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("submenu label appears in output")
val edit_sub = menu_with_submenu("tui_sub_edit_1", "Edit", [])
val bar = menubar_rich("tui_sub_bar_1", [edit_sub])
val rect = WidgetRect(id: "tui_sub_bar_1", x: 0, y: 0, w: 80, h: 1)
var screen = Screen.new(80, 1)
screen = render_tui_menubar(screen, bar, rect)
val row_text = screen.buffer[0]
expect row_text to_contain "Edit"
```

</details>

#### normal items still render correctly

- normal items still render correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normal items still render correctly")
val file_item = label("tui_norm_file_1", "File")
val bar = menubar_rich("tui_norm_bar_1", [file_item])
val rect = WidgetRect(id: "tui_norm_bar_1", x: 0, y: 0, w: 80, h: 1)
var screen = Screen.new(80, 1)
screen = render_tui_menubar(screen, bar, rect)
val row_text = screen.buffer[0]
expect row_text to_contain "File"
```

</details>

### HTML menubar separator rendering

#### separator has menu-separator class

- separator has menu-separator class


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("separator has menu-separator class")
val file_item = label("html_sep_file_1", "File")
val sep = menu_separator("html_sep_sep_1")
val bar = menubar_rich("html_sep_bar_1", [file_item, sep])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "menu-separator"
```

</details>

#### submenu has submenu class

- submenu has submenu class


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("submenu has submenu class")
val cut = label("html_sub_cut_1", "Cut")
val edit_sub = menu_with_submenu("html_sub_edit_1", "Edit", [cut])
val bar = menubar_rich("html_sub_bar_1", [edit_sub])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "submenu"
```

</details>

#### submenu has has-submenu class on menu-item

- submenu has has-submenu class on menu-item


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("submenu has has-submenu class on menu-item")
val cut = label("html_sub_cut_2", "Cut")
val edit_sub = menu_with_submenu("html_sub_edit_2", "Edit", [cut])
val bar = menubar_rich("html_sub_bar_2", [edit_sub])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "has-submenu"
```

</details>

#### normal items still have menu-item class

- normal items still have menu-item class


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normal items still have menu-item class")
val file_item = label("html_norm_file_1", "File")
val bar = menubar_rich("html_norm_bar_1", [file_item])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "menu-item"
```

</details>

### Tooltip builder

#### creates widget with content and target props

- creates widget with content and target props


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates widget with content and target props")
val tt = tooltip("tt_build_1", "Help text", "btn_1")
expect tt.get_prop("content") to_equal "Help text"
expect tt.get_prop("target") to_equal "btn_1"
```

</details>

#### has kind tooltip

- has kind tooltip


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has kind tooltip")
val tt = tooltip("tt_build_2", "Info", "link_1")
expect tt.kind_name() to_equal "tooltip"
```

</details>

### TUI tooltip rendering

#### output is NOT empty after fix

- output is NOT empty after fix


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output is NOT empty after fix")
val tt = tooltip("tui_tt_fix_1", "Click to submit", "submit_btn")
val rect = WidgetRect(id: "tui_tt_fix_1", x: 0, y: 0, w: 80, h: 1)
var screen = Screen.new(80, 1)
screen = render_tui_tooltip(screen, tt, rect)
val row_text = screen.buffer[0]
expect row_text to_contain "[?]"
```

</details>

#### output contains content text

- output contains content text


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains content text")
val tt = tooltip("tui_tt_fix_2", "Click to submit", "submit_btn_2")
val rect = WidgetRect(id: "tui_tt_fix_2", x: 0, y: 0, w: 80, h: 1)
var screen = Screen.new(80, 1)
screen = render_tui_tooltip(screen, tt, rect)
val row_text = screen.buffer[0]
expect row_text to_contain "Click to submit"
```

</details>

#### renders at correct position

- renders at correct position


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders at correct position")
val tt = tooltip("tui_tt_pos_1", "Tip", "tgt_1")
val rect = WidgetRect(id: "tui_tt_pos_1", x: 5, y: 2, w: 40, h: 1)
var screen = Screen.new(80, 5)
screen = render_tui_tooltip(screen, tt, rect)
val row_text = screen.buffer[2]
expect row_text to_contain "[?]"
```

</details>

### HTML tooltip rendering

#### contains tooltip-trigger span

- contains tooltip-trigger span


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains tooltip-trigger span")
val tt = tooltip("html_tt_trig_1", "Info here", "info_btn")
val tree = build_tree(tt)
val state = init_state(tree)
val html = render_html_widget(tt, state)
expect html to_contain "tooltip-trigger"
```

</details>

#### contains tooltip-content span

- contains tooltip-content span


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains tooltip-content span")
val tt = tooltip("html_tt_cont_1", "Info here", "info_btn_2")
val tree = build_tree(tt)
val state = init_state(tree)
val html = render_html_widget(tt, state)
expect html to_contain "tooltip-content"
```

</details>

#### trigger contains question mark

- trigger contains question mark


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trigger contains question mark")
val tt = tooltip("html_tt_qmark_1", "Details", "det_btn")
val tree = build_tree(tt)
val state = init_state(tree)
val html = render_html_widget(tt, state)
expect html to_contain "[?]"
```

</details>

#### content span contains tooltip text

- content span contains tooltip text


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("content span contains tooltip text")
val tt = tooltip("html_tt_text_1", "Press Enter to save", "save_btn")
val tree = build_tree(tt)
val state = init_state(tree)
val html = render_html_widget(tt, state)
expect html to_contain "Press Enter to save"
```

</details>

#### output contains data-target attribute

- output contains data-target attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains data-target attribute")
val tt = tooltip("html_tt_dtar_1", "Tip", "my_target")
val tree = build_tree(tt)
val state = init_state(tree)
val html = render_html_widget(tt, state)
expect html to_contain "data-target=\"my_target\""
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/widget_menu_tooltip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering menu_separator builder, menu_with_submenu builder, menubar_rich builder, TUI menubar separator rendering, HTML menubar separator rendering, Tooltip builder, TUI tooltip rendering, HTML tooltip rendering.
- menu_separator builder
- menu_with_submenu builder
- menubar_rich builder
- TUI menubar separator rendering
- HTML menubar separator rendering
- Tooltip builder
- TUI tooltip rendering
- HTML tooltip rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
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

- Canonical SPipe generation for source `73e3e4b547874531d28e508f6febaad044082d1b580925ca275166af7fbe32bb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `73e3e4b547874531d28e508f6febaad044082d1b580925ca275166af7fbe32bb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `73e3e4b547874531d28e508f6febaad044082d1b580925ca275166af7fbe32bb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/widget_menu_tooltip_spec.spl
mirror: doc/06_spec/unit/app/ui/widget_menu_tooltip_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/widget_menu_tooltip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/widget_menu_tooltip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/widget_menu_tooltip_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a text widget' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/widget_menu_tooltip_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has is_separator prop set to true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/widget_menu_tooltip_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has label set to pipe character' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
