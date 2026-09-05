# Widget Scroll Textarea Specification

> Tests covering Scroll widget creation, Scroll widget HTML rendering, Textarea widget creation, Textarea widget HTML rendering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Scroll Textarea Specification

## Scenarios

### Scroll widget creation

#### creates a widget with kind scroll

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates a widget with kind scroll


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a widget with kind scroll")
val child1 = text_widget("sc_child_k1", "Line 1")
val sc = scroll("sc_kind_1", 5, [child1])
expect sc.kind_name() to_equal "scroll"
```

</details>

#### stores the correct id

- stores the correct id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores the correct id")
val sc = scroll("sc_id_1", 5, [])
expect sc.id to_equal "sc_id_1"
```

</details>

#### stores max_height prop

- stores max_height prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores max_height prop")
val sc = scroll("sc_maxh_1", 5, [])
expect sc.get_prop("max_height") to_equal "5"
```

</details>

#### stores scroll_offset prop defaulting to 0

- stores scroll_offset prop defaulting to 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores scroll_offset prop defaulting to 0")
val sc = scroll("sc_offset_1", 10, [])
expect sc.get_prop("scroll_offset") to_equal "0"
```

</details>

#### has correct child count for three children

- has correct child count for three children


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct child count for three children")
val c1 = text_widget("sc_cc_c1", "A")
val c2 = text_widget("sc_cc_c2", "B")
val c3 = text_widget("sc_cc_c3", "C")
val sc = scroll("sc_cc_1", 5, [c1, c2, c3])
expect sc.child_count() to_equal 3
```

</details>

#### has zero children when created empty

- has zero children when created empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has zero children when created empty")
val sc = scroll("sc_empty_1", 5, [])
expect sc.child_count() to_equal 0
```

</details>

#### children are added correctly

- children are added correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("children are added correctly")
val c1 = text_widget("sc_add_c1", "First")
val c2 = text_widget("sc_add_c2", "Second")
val sc = scroll("sc_add_1", 8, [c1, c2])
val first = sc.child_at(0)
expect first != nil to_equal true
expect first.get_prop("content") to_equal "First"
```

</details>

#### defaults visible to true

- defaults visible to true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults visible to true")
val sc = scroll("sc_vis_1", 5, [])
expect sc.is_visible() to_equal true
```

</details>

#### defaults focused to false

- defaults focused to false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults focused to false")
val sc = scroll("sc_foc_1", 5, [])
expect sc.is_focused() to_equal false
```

</details>

#### has max_height and scroll_offset in prop_keys

- has max_height and scroll_offset in prop_keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has max_height and scroll_offset in prop_keys")
val sc = scroll("sc_keys_1", 5, [])
val keys = sc.prop_keys()
expect keys to_contain "max_height"
expect keys to_contain "scroll_offset"
```

</details>

#### has_prop returns true for max_height

- has_prop returns true for max_height


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_prop returns true for max_height")
val sc = scroll("sc_hasprop_1", 5, [])
expect sc.has_prop("max_height") to_equal true
```

</details>

#### has_prop returns false for nonexistent key

- has_prop returns false for nonexistent key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_prop returns false for nonexistent key")
val sc = scroll("sc_hasprop_2", 5, [])
expect sc.has_prop("tooltip") to_equal false
```

</details>

### Scroll widget HTML rendering

#### renders with widget-scroll class

- renders with widget-scroll class


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders with widget-scroll class")
val c1 = text_widget("sc_html_c1", "Item")
val sc = scroll("sc_html_1", 5, [c1])
val tree = UITree.new(sc)
val state = init_state(tree)
val html = render_html_widget(sc, state)
expect html to_contain "widget-scroll"
```

</details>

#### renders with overflow-y style

- renders with overflow-y style


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders with overflow-y style")
val c1 = text_widget("sc_html_ov_c1", "Item")
val sc = scroll("sc_html_ov_1", 5, [c1])
val tree = UITree.new(sc)
val state = init_state(tree)
val html = render_html_widget(sc, state)
expect html to_contain "overflow-y"
```

</details>

#### renders with max-height style

- renders with max-height style


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders with max-height style")
val c1 = text_widget("sc_html_mh_c1", "Item")
val sc = scroll("sc_html_mh_1", 5, [c1])
val tree = UITree.new(sc)
val state = init_state(tree)
val html = render_html_widget(sc, state)
expect html to_contain "max-height:5px"
```

</details>

#### renders children inside the scroll div

- renders children inside the scroll div


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders children inside the scroll div")
val c1 = text_widget("sc_html_ch_c1", "Scroll Child")
val sc = scroll("sc_html_ch_1", 10, [c1])
val tree = UITree.new(sc)
val state = init_state(tree)
val html = render_html_widget(sc, state)
expect html to_contain "Scroll Child"
```

</details>

#### includes widget id attribute

- includes widget id attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes widget id attribute")
val sc = scroll("sc_html_id_1", 5, [])
val tree = UITree.new(sc)
val state = init_state(tree)
val html = render_html_widget(sc, state)
expect html to_contain "id=\"sc_html_id_1\""
```

</details>

#### adds focused class when scroll is focused

- adds focused class when scroll is focused


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds focused class when scroll is focused")
val sc = scroll("sc_html_focus_1", 5, [])
val tree = UITree.new(sc)
val state = init_state(tree)
expect state.focused_id to_equal "sc_html_focus_1"
val html = render_html_widget(sc, state)
expect html to_contain "focused"
```

</details>

#### does not add focused class when scroll is not focused

- does not add focused class when scroll is not focused


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not add focused class when scroll is not focused")
val sc = scroll("sc_html_nofocus_1", 5, [])
val root = panel("sc_html_nofocus_root", "Panel", [sc])
val tree = UITree.new(root)
val state = init_state(tree)
expect state.focused_id to_equal "sc_html_nofocus_root"
val html = render_html_widget(sc, state)
val has_focused = html.contains("focused")
expect has_focused to_equal false
```

</details>

#### starts with opening div tag

- starts with opening div tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with opening div tag")
val sc = scroll("sc_html_div_1", 5, [])
val tree = UITree.new(sc)
val state = init_state(tree)
val html = render_html_widget(sc, state)
expect html.starts_with("<div") to_equal true
```

</details>

#### ends with closing div tag

- ends with closing div tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ends with closing div tag")
val sc = scroll("sc_html_close_1", 5, [])
val tree = UITree.new(sc)
val state = init_state(tree)
val html = render_html_widget(sc, state)
expect html.ends_with("</div>") to_equal true
```

</details>

### Textarea widget creation

#### creates a widget with kind textarea

- creates a widget with kind textarea


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a widget with kind textarea")
val ta = textarea("ta_kind_1", "hello", "Type here", 5)
expect ta.kind_name() to_equal "textarea"
```

</details>

#### stores the correct id

- stores the correct id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores the correct id")
val ta = textarea("ta_id_1", "content", "", 3)
expect ta.id to_equal "ta_id_1"
```

</details>

#### stores value prop with multi-line text

- stores value prop with multi-line text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores value prop with multi-line text")
val ta = textarea("ta_val_1", "hello\nworld", "Type here", 5)
expect ta.get_prop("value") to_contain "hello"
expect ta.get_prop("value") to_contain "world"
```

</details>

#### stores rows prop

- stores rows prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores rows prop")
val ta = textarea("ta_rows_1", "", "", 5)
expect ta.get_prop("rows") to_equal "5"
```

</details>

#### stores placeholder prop

- stores placeholder prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores placeholder prop")
val ta = textarea("ta_ph_1", "", "Type here", 5)
expect ta.get_prop("placeholder") to_equal "Type here"
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
val ta = textarea("ta_nochild_1", "text", "", 3)
expect ta.child_count() to_equal 0
```

</details>

#### defaults visible to true

- defaults visible to true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults visible to true")
val ta = textarea("ta_vis_1", "", "", 3)
expect ta.is_visible() to_equal true
```

</details>

#### defaults focused to false

- defaults focused to false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults focused to false")
val ta = textarea("ta_foc_1", "", "", 3)
expect ta.is_focused() to_equal false
```

</details>

#### has value, placeholder, and rows in prop_keys

- has value, placeholder, and rows in prop_keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has value, placeholder, and rows in prop_keys")
val ta = textarea("ta_keys_1", "text", "hint", 5)
val keys = ta.prop_keys()
expect keys to_contain "value"
expect keys to_contain "placeholder"
expect keys to_contain "rows"
```

</details>

#### has_prop returns true for value

- has_prop returns true for value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_prop returns true for value")
val ta = textarea("ta_hasprop_1", "text", "", 3)
expect ta.has_prop("value") to_equal true
```

</details>

#### has_prop returns false for nonexistent key

- has_prop returns false for nonexistent key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_prop returns false for nonexistent key")
val ta = textarea("ta_hasprop_2", "text", "", 3)
expect ta.has_prop("tooltip") to_equal false
```

</details>

### Textarea widget HTML rendering

#### renders with widget-textarea class

- renders with widget-textarea class


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders with widget-textarea class")
val ta = textarea("ta_html_1", "hello", "", 3)
val tree = UITree.new(ta)
val state = init_state(tree)
val html = render_html_widget(ta, state)
expect html to_contain "widget-textarea"
```

</details>

#### renders as a textarea tag

- renders as a textarea tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders as a textarea tag")
val ta = textarea("ta_html_tag_1", "hello", "", 3)
val tree = UITree.new(ta)
val state = init_state(tree)
val html = render_html_widget(ta, state)
expect html.starts_with("<textarea") to_equal true
```

</details>

#### includes rows attribute

- includes rows attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes rows attribute")
val ta = textarea("ta_html_rows_1", "hello", "", 5)
val tree = UITree.new(ta)
val state = init_state(tree)
val html = render_html_widget(ta, state)
expect html to_contain "rows=\"5\""
```

</details>

#### includes placeholder attribute

- includes placeholder attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes placeholder attribute")
val ta = textarea("ta_html_ph_1", "", "Type here", 3)
val tree = UITree.new(ta)
val state = init_state(tree)
val html = render_html_widget(ta, state)
expect html to_contain "placeholder=\"Type here\""
```

</details>

#### includes value as content

- includes value as content


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes value as content")
val ta = textarea("ta_html_val_1", "hello world", "", 3)
val tree = UITree.new(ta)
val state = init_state(tree)
val html = render_html_widget(ta, state)
expect html to_contain "hello world"
```

</details>

#### includes widget id attribute

- includes widget id attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes widget id attribute")
val ta = textarea("ta_html_id_1", "", "", 3)
val tree = UITree.new(ta)
val state = init_state(tree)
val html = render_html_widget(ta, state)
expect html to_contain "id=\"ta_html_id_1\""
```

</details>

#### adds focused class when textarea is focused

- adds focused class when textarea is focused


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds focused class when textarea is focused")
val ta = textarea("ta_html_focus_1", "text", "", 3)
val tree = UITree.new(ta)
val state = init_state(tree)
expect state.focused_id to_equal "ta_html_focus_1"
val html = render_html_widget(ta, state)
expect html to_contain "focused"
```

</details>

#### does not add focused class when textarea is not focused

- does not add focused class when textarea is not focused


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not add focused class when textarea is not focused")
val ta = textarea("ta_html_nofocus_1", "text", "", 3)
val root = panel("ta_html_nofocus_root", "Panel", [ta])
val tree = UITree.new(root)
val state = init_state(tree)
expect state.focused_id to_equal "ta_html_nofocus_root"
val html = render_html_widget(ta, state)
val has_focused = html.contains("focused")
expect has_focused to_equal false
```

</details>

#### ends with closing textarea tag

- ends with closing textarea tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ends with closing textarea tag")
val ta = textarea("ta_html_close_1", "text", "", 3)
val tree = UITree.new(ta)
val state = init_state(tree)
val html = render_html_widget(ta, state)
expect html.ends_with("</textarea>") to_equal true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/widget_scroll_textarea_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Scroll widget creation, Scroll widget HTML rendering, Textarea widget creation, Textarea widget HTML rendering.
- Scroll widget creation
- Scroll widget HTML rendering
- Textarea widget creation
- Textarea widget HTML rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
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

- Canonical SPipe generation for source `0a074d3e5f2f8d1b226855a819659f3bc3a6066a50f94125f988b0b39c19cbf7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0a074d3e5f2f8d1b226855a819659f3bc3a6066a50f94125f988b0b39c19cbf7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0a074d3e5f2f8d1b226855a819659f3bc3a6066a50f94125f988b0b39c19cbf7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/widget_scroll_textarea_spec.spl
mirror: doc/06_spec/unit/app/ui/widget_scroll_textarea_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/widget_scroll_textarea_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/widget_scroll_textarea_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/widget_scroll_textarea_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a widget with kind scroll' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/widget_scroll_textarea_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores the correct id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/widget_scroll_textarea_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores max_height prop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
