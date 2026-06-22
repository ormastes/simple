# Widget Scroll Textarea Specification

> 1. expect sc kind name

<!-- sdn-diagram:id=widget_scroll_textarea_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_scroll_textarea_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_scroll_textarea_spec -> common
widget_scroll_textarea_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_scroll_textarea_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Scroll Textarea Specification

## Scenarios

### Scroll widget creation

#### creates a widget with kind scroll

1. expect sc kind name


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val child1 = text_widget("sc_child_k1", "Line 1")
val sc = scroll("sc_kind_1", 5, [child1])
expect sc.kind_name() to_equal "scroll"
```

</details>

#### stores the correct id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sc = scroll("sc_id_1", 5, [])
expect sc.id to_equal "sc_id_1"
```

</details>

#### stores max_height prop

1. expect sc get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sc = scroll("sc_maxh_1", 5, [])
expect sc.get_prop("max_height") to_equal "5"
```

</details>

#### stores scroll_offset prop defaulting to 0

1. expect sc get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sc = scroll("sc_offset_1", 10, [])
expect sc.get_prop("scroll_offset") to_equal "0"
```

</details>

#### has correct child count for three children

1. expect sc child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = text_widget("sc_cc_c1", "A")
val c2 = text_widget("sc_cc_c2", "B")
val c3 = text_widget("sc_cc_c3", "C")
val sc = scroll("sc_cc_1", 5, [c1, c2, c3])
expect sc.child_count() to_equal 3
```

</details>

#### has zero children when created empty

1. expect sc child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sc = scroll("sc_empty_1", 5, [])
expect sc.child_count() to_equal 0
```

</details>

#### children are added correctly

1. expect first get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = text_widget("sc_add_c1", "First")
val c2 = text_widget("sc_add_c2", "Second")
val sc = scroll("sc_add_1", 8, [c1, c2])
val first = sc.child_at(0)
expect first != nil to_equal true
expect first.get_prop("content") to_equal "First"
```

</details>

#### defaults visible to true

1. expect sc is visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sc = scroll("sc_vis_1", 5, [])
expect sc.is_visible() to_equal true
```

</details>

#### defaults focused to false

1. expect sc is focused


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sc = scroll("sc_foc_1", 5, [])
expect sc.is_focused() to_equal false
```

</details>

#### has max_height and scroll_offset in prop_keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sc = scroll("sc_keys_1", 5, [])
val keys = sc.prop_keys()
expect keys to_contain "max_height"
expect keys to_contain "scroll_offset"
```

</details>

#### has_prop returns true for max_height

1. expect sc has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sc = scroll("sc_hasprop_1", 5, [])
expect sc.has_prop("max_height") to_equal true
```

</details>

#### has_prop returns false for nonexistent key

1. expect sc has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sc = scroll("sc_hasprop_2", 5, [])
expect sc.has_prop("tooltip") to_equal false
```

</details>

### Scroll widget HTML rendering

#### renders with widget-scroll class

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = text_widget("sc_html_c1", "Item")
val sc = scroll("sc_html_1", 5, [c1])
val tree = UITree.new(sc)
val state = init_state(tree)
val html = render_html_widget(sc, state)
expect html to_contain "widget-scroll"
```

</details>

#### renders with overflow-y style

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = text_widget("sc_html_ov_c1", "Item")
val sc = scroll("sc_html_ov_1", 5, [c1])
val tree = UITree.new(sc)
val state = init_state(tree)
val html = render_html_widget(sc, state)
expect html to_contain "overflow-y"
```

</details>

#### renders with max-height style

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = text_widget("sc_html_mh_c1", "Item")
val sc = scroll("sc_html_mh_1", 5, [c1])
val tree = UITree.new(sc)
val state = init_state(tree)
val html = render_html_widget(sc, state)
expect html to_contain "max-height:5px"
```

</details>

#### renders children inside the scroll div

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = text_widget("sc_html_ch_c1", "Scroll Child")
val sc = scroll("sc_html_ch_1", 10, [c1])
val tree = UITree.new(sc)
val state = init_state(tree)
val html = render_html_widget(sc, state)
expect html to_contain "Scroll Child"
```

</details>

#### includes widget id attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sc = scroll("sc_html_id_1", 5, [])
val tree = UITree.new(sc)
val state = init_state(tree)
val html = render_html_widget(sc, state)
expect html to_contain "id=\"sc_html_id_1\""
```

</details>

#### adds focused class when scroll is focused

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sc = scroll("sc_html_focus_1", 5, [])
val tree = UITree.new(sc)
val state = init_state(tree)
expect state.focused_id to_equal "sc_html_focus_1"
val html = render_html_widget(sc, state)
expect html to_contain "focused"
```

</details>

#### does not add focused class when scroll is not focused

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect html starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sc = scroll("sc_html_div_1", 5, [])
val tree = UITree.new(sc)
val state = init_state(tree)
val html = render_html_widget(sc, state)
expect html.starts_with("<div") to_equal true
```

</details>

#### ends with closing div tag

1. expect html ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sc = scroll("sc_html_close_1", 5, [])
val tree = UITree.new(sc)
val state = init_state(tree)
val html = render_html_widget(sc, state)
expect html.ends_with("</div>") to_equal true
```

</details>

### Textarea widget creation

#### creates a widget with kind textarea

1. expect ta kind name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ta = textarea("ta_kind_1", "hello", "Type here", 5)
expect ta.kind_name() to_equal "textarea"
```

</details>

#### stores the correct id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ta = textarea("ta_id_1", "content", "", 3)
expect ta.id to_equal "ta_id_1"
```

</details>

#### stores value prop with multi-line text

1. expect ta get prop
2. expect ta get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ta = textarea("ta_val_1", "hello\nworld", "Type here", 5)
expect ta.get_prop("value") to_contain "hello"
expect ta.get_prop("value") to_contain "world"
```

</details>

#### stores rows prop

1. expect ta get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ta = textarea("ta_rows_1", "", "", 5)
expect ta.get_prop("rows") to_equal "5"
```

</details>

#### stores placeholder prop

1. expect ta get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ta = textarea("ta_ph_1", "", "Type here", 5)
expect ta.get_prop("placeholder") to_equal "Type here"
```

</details>

#### has no children

1. expect ta child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ta = textarea("ta_nochild_1", "text", "", 3)
expect ta.child_count() to_equal 0
```

</details>

#### defaults visible to true

1. expect ta is visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ta = textarea("ta_vis_1", "", "", 3)
expect ta.is_visible() to_equal true
```

</details>

#### defaults focused to false

1. expect ta is focused


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ta = textarea("ta_foc_1", "", "", 3)
expect ta.is_focused() to_equal false
```

</details>

#### has value, placeholder, and rows in prop_keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ta = textarea("ta_keys_1", "text", "hint", 5)
val keys = ta.prop_keys()
expect keys to_contain "value"
expect keys to_contain "placeholder"
expect keys to_contain "rows"
```

</details>

#### has_prop returns true for value

1. expect ta has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ta = textarea("ta_hasprop_1", "text", "", 3)
expect ta.has_prop("value") to_equal true
```

</details>

#### has_prop returns false for nonexistent key

1. expect ta has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ta = textarea("ta_hasprop_2", "text", "", 3)
expect ta.has_prop("tooltip") to_equal false
```

</details>

### Textarea widget HTML rendering

#### renders with widget-textarea class

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ta = textarea("ta_html_1", "hello", "", 3)
val tree = UITree.new(ta)
val state = init_state(tree)
val html = render_html_widget(ta, state)
expect html to_contain "widget-textarea"
```

</details>

#### renders as a textarea tag

1. expect html starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ta = textarea("ta_html_tag_1", "hello", "", 3)
val tree = UITree.new(ta)
val state = init_state(tree)
val html = render_html_widget(ta, state)
expect html.starts_with("<textarea") to_equal true
```

</details>

#### includes rows attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ta = textarea("ta_html_rows_1", "hello", "", 5)
val tree = UITree.new(ta)
val state = init_state(tree)
val html = render_html_widget(ta, state)
expect html to_contain "rows=\"5\""
```

</details>

#### includes placeholder attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ta = textarea("ta_html_ph_1", "", "Type here", 3)
val tree = UITree.new(ta)
val state = init_state(tree)
val html = render_html_widget(ta, state)
expect html to_contain "placeholder=\"Type here\""
```

</details>

#### includes value as content

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ta = textarea("ta_html_val_1", "hello world", "", 3)
val tree = UITree.new(ta)
val state = init_state(tree)
val html = render_html_widget(ta, state)
expect html to_contain "hello world"
```

</details>

#### includes widget id attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ta = textarea("ta_html_id_1", "", "", 3)
val tree = UITree.new(ta)
val state = init_state(tree)
val html = render_html_widget(ta, state)
expect html to_contain "id=\"ta_html_id_1\""
```

</details>

#### adds focused class when textarea is focused

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ta = textarea("ta_html_focus_1", "text", "", 3)
val tree = UITree.new(ta)
val state = init_state(tree)
expect state.focused_id to_equal "ta_html_focus_1"
val html = render_html_widget(ta, state)
expect html to_contain "focused"
```

</details>

#### does not add focused class when textarea is not focused

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect html ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/ui/widget_scroll_textarea_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
