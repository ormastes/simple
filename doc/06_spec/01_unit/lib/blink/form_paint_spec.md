# Blink Form Paint Specification

> Purpose: Prove that form_state data type.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink Form Paint Specification

Purpose: Prove that form_state data type.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink / Paint |
| Status | Active |
| Source | `test/01_unit/lib/blink/form_paint_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that form_state data type.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### form_state data type

#### set_value then get_value round-trips

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- set_value then get_value round-trips
- Verify: set_value then get_value round-trips
   - Expected: form_state_get_value(s1, 42) equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("set_value then get_value round-trips")
step("Verify: set_value then get_value round-trips")
# @req: REQ-LIB-BLINK-001
val s0 = form_state_empty()
val s1 = form_state_set_value(s0, 42, "hello")
expect(form_state_get_value(s1, 42)).to_equal("hello")
```

</details>

#### get_value returns empty string for absent node

- get_value returns empty string for absent node
- Verify: get_value returns empty string for absent node
   - Expected: form_state_get_value(s0, 99) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("get_value returns empty string for absent node")
step("Verify: get_value returns empty string for absent node")
val s0 = form_state_empty()
expect(form_state_get_value(s0, 99)).to_equal("")
```

</details>

#### with_field replaces existing entry for same node_id

- with_field replaces existing entry for same node_id
- Verify: with_field replaces existing entry for same node_id
   - Expected: form_state_get_value(s2, 5) equals `two`
   - Expected: form_state_get_placeholder(s2, 5) equals `ph2`
   - Expected: s2.fields.len().to_i64() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("with_field replaces existing entry for same node_id")
step("Verify: with_field replaces existing entry for same node_id")
val s0 = form_state_empty()
val e1 = FormFieldEntry(node_id: 5, value: "one", placeholder: "ph")
val s1 = form_state_with_field(s0, e1)
val e2 = FormFieldEntry(node_id: 5, value: "two", placeholder: "ph2")
val s2 = form_state_with_field(s1, e2)
expect(form_state_get_value(s2, 5)).to_equal("two")
expect(form_state_get_placeholder(s2, 5)).to_equal("ph2")
expect(s2.fields.len().to_i64()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### set_value preserves placeholder when a prior entry existed

- set_value preserves placeholder when a prior entry existed
- Verify: set_value preserves placeholder when a prior entry existed
   - Expected: form_state_get_value(s2, 7) equals `typed`
   - Expected: form_state_get_placeholder(s2, 7) equals `search…`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("set_value preserves placeholder when a prior entry existed")
step("Verify: set_value preserves placeholder when a prior entry existed")
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

- emits fill + border + text for an input with a value
- Verify: emits fill + border + text for an input with a value
   - Expected: dl.ops.len().to_i64() >= 3 is true
   - Expected: count_fill_rect_ops(dl) equals `1`
   - Expected: count_draw_border_ops(dl) equals `1`
   - Expected: count_draw_text_with(dl, "hello") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("emits fill + border + text for an input with a value")
step("Verify: emits fill + border + text for an input with a value")
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
expect(count_fill_rect_ops(dl)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(count_draw_border_ops(dl)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(count_draw_text_with(dl, "hello")).to_equal(1)
```

</details>

#### draws placeholder text when value is empty

- draws placeholder text when value is empty
- Verify: draws placeholder text when value is empty
   - Expected: count_draw_text_with(dl, "search…") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draws placeholder text when value is empty")
step("Verify: draws placeholder text when value is empty")
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

- focused input border differs from unfocused input border
- Verify: focused input border differs from unfocused input border
   - Expected: snap_u_opt is None is false
   - Expected: snap_f_opt is None is false
   - Expected: colors_differ or widths_differ is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("focused input border differs from unfocused input border")
step("Verify: focused input border differs from unfocused input border")
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

- emits fill + text for a button
- Verify: emits fill + text for a button
   - Expected: dl.ops.len().to_i64() >= 2 is true
   - Expected: count_fill_rect_ops(dl) equals `1`
   - Expected: count_draw_text_with(dl, "Click me") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("emits fill + text for a button")
step("Verify: emits fill + text for a button")
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
expect(count_fill_rect_ops(dl)).to_equal(1)  # oracle: 1 — named expected value from the requirement
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-BLINK-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1de36cd27df08cf04f0694e9538ade6326626a0ae1475f894cf6d9a8ab7111ef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1de36cd27df08cf04f0694e9538ade6326626a0ae1475f894cf6d9a8ab7111ef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1de36cd27df08cf04f0694e9538ade6326626a0ae1475f894cf6d9a8ab7111ef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/blink/form_paint_spec.spl
mirror: doc/06_spec/01_unit/lib/blink/form_paint_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/blink/form_paint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/blink/form_paint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/blink/form_paint_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/blink/form_paint_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'set_value then get_value round-trips' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/form_paint_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'get_value returns empty string for absent node' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/form_paint_spec.spl:147:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'with_field replaces existing entry for same node_id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
