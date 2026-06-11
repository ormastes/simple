# Blink Form Paint Specification

> Tests the Phase B3 form-control paint path: <input> and <button> elements registered on the paint walker must emit their composite paint ops (background fill, optional border, text) in the correct order. Focused <input> borders must use the accent color distinct from the unfocused outline color. Also covers the FormState immutable data type.

<!-- sdn-diagram:id=form_paint_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=form_paint_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

form_paint_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=form_paint_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink Form Paint Specification

Tests the Phase B3 form-control paint path: <input> and <button> elements registered on the paint walker must emit their composite paint ops (background fill, optional border, text) in the correct order. Focused <input> borders must use the accent color distinct from the unfocused outline color. Also covers the FormState immutable data type.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink / Paint |
| Status | Active |
| Source | `test/01_unit/lib/blink/form_paint_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the Phase B3 form-control paint path: <input> and <button> elements
registered on the paint walker must emit their composite paint ops
(background fill, optional border, text) in the correct order. Focused
<input> borders must use the accent color distinct from the unfocused
outline color. Also covers the FormState immutable data type.

## Scenarios

### form_state data type

#### set_value then get_value round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s0 = form_state_empty()
val s1 = form_state_set_value(s0, 42, "hello")
expect(form_state_get_value(s1, 42)).to_equal("hello")
```

</details>

#### get_value returns empty string for absent node

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s0 = form_state_empty()
expect(form_state_get_value(s0, 99)).to_equal("")
```

</details>

#### with_field replaces existing entry for same node_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s0 = form_state_empty()
val e1 = FormFieldEntry(node_id: 5, value: "one", placeholder: "ph")
val s1 = form_state_with_field(s0, e1)
val e2 = FormFieldEntry(node_id: 5, value: "two", placeholder: "ph2")
val s2 = form_state_with_field(s1, e2)
expect(form_state_get_value(s2, 5)).to_equal("two")
expect(form_state_get_placeholder(s2, 5)).to_equal("ph2")
expect(s2.fields.len().to_i64()).to_equal(1)
```

</details>

#### set_value preserves placeholder when a prior entry existed

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s0 = form_state_empty()
val entry = FormFieldEntry(node_id: 7, value: "", placeholder: "search…")
val s1 = form_state_with_field(s0, entry)
val s2 = form_state_set_value(s1, 7, "typed")
expect(form_state_get_value(s2, 7)).to_equal("typed")
expect(form_state_get_placeholder(s2, 7)).to_equal("search…")
```

</details>

### paint walker <input> emission

#### emits fill + border + text for an input with a value

1. pc paint box
   - Expected: dl.ops.len().to_i64() >= 3 is true
   - Expected: count_fill_rect_ops(dl) equals `1`
   - Expected: count_draw_border_ops(dl) equals `1`
   - Expected: count_draw_text_with(dl, "hello") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = make_single_box_ctx(10, 160.0, 32.0)
val styles = [StyledBox]()
val fields = [FormFieldPaintEntry]()
fields.push(FormFieldPaintEntry(
    layout_id: 10,
    value: "hello",
    placeholder: "",
    label: "",
    is_button: false,
    node_id: 10
))
val pc = paint_tree_new_with_forms(ctx, styles, fields, interaction_state_empty())
pc.paint_box(10, 0.0, 0.0)
val dl = collect_display_list(pc)
expect(dl.ops.len().to_i64() >= 3).to_equal(true)
expect(count_fill_rect_ops(dl)).to_equal(1)
expect(count_draw_border_ops(dl)).to_equal(1)
expect(count_draw_text_with(dl, "hello")).to_equal(1)
```

</details>

#### draws placeholder text when value is empty

1. pc paint box
   - Expected: count_draw_text_with(dl, "search…") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = make_single_box_ctx(20, 160.0, 32.0)
val styles = [StyledBox]()
val fields = [FormFieldPaintEntry]()
fields.push(FormFieldPaintEntry(
    layout_id: 20,
    value: "",
    placeholder: "search…",
    label: "",
    is_button: false,
    node_id: 20
))
val pc = paint_tree_new_with_forms(ctx, styles, fields, interaction_state_empty())
pc.paint_box(20, 0.0, 0.0)
val dl = collect_display_list(pc)
expect(count_draw_text_with(dl, "search…")).to_equal(1)
```

</details>

#### focused input border differs from unfocused input border

1. pc u paint box
2. pc f paint box
   - Expected: snap_u_opt is None is false
   - Expected: snap_f_opt is None is false
   - Expected: colors_differ or widths_differ is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = make_single_box_ctx(30, 160.0, 32.0)
val styles = [StyledBox]()
val fields_a = [FormFieldPaintEntry]()
fields_a.push(FormFieldPaintEntry(
    layout_id: 30,
    value: "x",
    placeholder: "",
    label: "",
    is_button: false,
    node_id: 30
))
# Unfocused walk
val pc_u = paint_tree_new_with_forms(ctx, styles, fields_a, interaction_state_empty())
pc_u.paint_box(30, 0.0, 0.0)
val dl_u = collect_display_list(pc_u)
val snap_u_opt = first_border_color(dl_u)

# Focused walk — new ctx because compute_layout was already applied,
# but we can reuse the same one safely: the walker only appends ops.
val fields_b = [FormFieldPaintEntry]()
fields_b.push(FormFieldPaintEntry(
    layout_id: 30,
    value: "x",
    placeholder: "",
    label: "",
    is_button: false,
    node_id: 30
))
val pc_f = paint_tree_new_with_forms(ctx, styles, fields_b, interaction_state_with_focus(30))
pc_f.paint_box(30, 0.0, 0.0)
val dl_f = collect_display_list(pc_f)
val snap_f_opt = first_border_color(dl_f)

expect(snap_u_opt is None).to_equal(false)
expect(snap_f_opt is None).to_equal(false)
if val snap_u = snap_u_opt:
    if val snap_f = snap_f_opt:
        val colors_differ = (snap_u.r != snap_f.r) or (snap_u.g != snap_f.g) or (snap_u.b != snap_f.b) or (snap_u.a != snap_f.a)
        val widths_differ = snap_u.width != snap_f.width
        expect(colors_differ or widths_differ).to_equal(true)
```

</details>

### paint walker <button> emission

#### emits fill + text for a button

1. pc paint box
   - Expected: dl.ops.len().to_i64() >= 2 is true
   - Expected: count_fill_rect_ops(dl) equals `1`
   - Expected: count_draw_text_with(dl, "Click me") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = make_single_box_ctx(40, 120.0, 32.0)
val styles = [StyledBox]()
val fields = [FormFieldPaintEntry]()
fields.push(FormFieldPaintEntry(
    layout_id: 40,
    value: "",
    placeholder: "",
    label: "Click me",
    is_button: true,
    node_id: 40
))
val pc = paint_tree_new_with_forms(ctx, styles, fields, interaction_state_empty())
pc.paint_box(40, 0.0, 0.0)
val dl = collect_display_list(pc)
expect(dl.ops.len().to_i64() >= 2).to_equal(true)
expect(count_fill_rect_ops(dl)).to_equal(1)
expect(count_draw_text_with(dl, "Click me")).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
