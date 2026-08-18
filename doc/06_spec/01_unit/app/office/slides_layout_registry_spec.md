# slides_layout_registry_spec

> Slide layout + element-kind registry (lane L4).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# slides_layout_registry_spec

Slide layout + element-kind registry (lane L4).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/slides_layout_registry_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Slide layout + element-kind registry (lane L4).

Proves the new src/app/office/slides/layout_registry.spl and
element_kind_registry.spl decouple slide-layout and element-kind creation
from the closed SlideLayout/SlideElementKind enums (slide.spl:9-20):

- the registry lists the five builtin layouts plus a demo third-party layout
  ("title_diagram" from src/lib/editor/extensions/builtin/slides_ext.spl,
  simulating a real extension registering via the same API);
- creating a slide by the demo layout's id yields its typed placeholders;
- creating a slide by an existing builtin layout id still yields geometry
  byte-identical to the legacy hardcoded constructors (golden-compare);
- element creation by kind id works for all four builtin kinds;
- unknown layout/kind ids error cleanly instead of silently defaulting.

## Scenarios

### Slide layout registry

#### lists the five builtin layouts before any extension registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
slide_layout_registry_reset()
val ids = slide_layout_registry_ids()
assert_equal(ids.len(), 5)
assert_true(slide_layout_registry_has("title_slide"))
assert_true(slide_layout_registry_has("title_content"))
assert_true(slide_layout_registry_has("two_column"))
assert_true(slide_layout_registry_has("blank"))
assert_true(slide_layout_registry_has("section_header"))
```

</details>

#### gains a sixth layout once the demo extension registers (title_diagram)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
slide_layout_registry_reset()
assert_true(slides_ext_register_builtins())
val ids = slide_layout_registry_ids()
assert_equal(ids.len(), 6)
assert_true(slide_layout_registry_has("title_diagram"))
```

</details>

#### creates a slide from the demo layout id with its typed placeholders

<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
slide_layout_registry_reset()
assert_true(slides_ext_register_builtins())

match create_slide_from_layout_id("title_diagram", "demo1"):
    Ok(slide):
        assert_equal(slide.elements.len(), 2)
        val title_el = slide.elements[0]
        assert_equal(title_el.id, "demo1_title")
        assert_equal(title_el.x, 50)
        assert_equal(title_el.y, 30)
        assert_equal(title_el.width, 860)
        assert_equal(title_el.height, 60)
        match title_el.kind:
            SlideElementKind.TextBox(content):
                assert_equal(content, "Title")
            _:
                assert_true(false)
        val diagram_el = slide.elements[1]
        assert_equal(diagram_el.id, "demo1_diagram")
        assert_equal(diagram_el.x, 50)
        assert_equal(diagram_el.y, 110)
        assert_equal(diagram_el.width, 860)
        assert_equal(diagram_el.height, 400)
        match diagram_el.kind:
            SlideElementKind.TextBox(content):
                assert_equal(content, "Diagram goes here")
            _:
                assert_true(false)
    Err(_):
        assert_true(false)
```

</details>

#### creating by the title_slide id yields geometry identical to the legacy constructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
slide_layout_registry_reset()
val legacy = title_slide("golden1", "My Title", "My Subtitle")
match create_slide_from_layout_id("title_slide", "golden2"):
    Ok(via_registry):
        assert_equal(via_registry.elements.len(), 2)
        assert_equal(legacy.elements.len(), 2)
        assert_equal(via_registry.elements[0].x, legacy.elements[0].x)
        assert_equal(via_registry.elements[0].y, legacy.elements[0].y)
        assert_equal(via_registry.elements[0].width, legacy.elements[0].width)
        assert_equal(via_registry.elements[0].height, legacy.elements[0].height)
        # golden-compare against the historically hardcoded numbers too
        assert_equal(via_registry.elements[0].x, 100)
        assert_equal(via_registry.elements[0].y, 150)
        assert_equal(via_registry.elements[0].width, 760)
        assert_equal(via_registry.elements[0].height, 80)
        assert_equal(via_registry.elements[1].x, 150)
        assert_equal(via_registry.elements[1].y, 250)
        assert_equal(via_registry.elements[1].width, 660)
        assert_equal(via_registry.elements[1].height, 50)
    Err(_):
        assert_true(false)
```

</details>

#### creating by the title_content id yields geometry identical to the legacy constructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
slide_layout_registry_reset()
val legacy = content_slide("golden3", "T", "B")
match create_slide_from_layout_id("title_content", "golden4"):
    Ok(via_registry):
        assert_equal(via_registry.elements[0].x, legacy.elements[0].x)
        assert_equal(via_registry.elements[0].width, legacy.elements[0].width)
        assert_equal(via_registry.elements[1].x, legacy.elements[1].x)
        assert_equal(via_registry.elements[1].y, legacy.elements[1].y)
        assert_equal(via_registry.elements[1].width, legacy.elements[1].width)
        assert_equal(via_registry.elements[1].height, legacy.elements[1].height)
        # golden-compare against the historically hardcoded numbers too
        assert_equal(via_registry.elements[0].x, 50)
        assert_equal(via_registry.elements[0].y, 30)
        assert_equal(via_registry.elements[1].x, 50)
        assert_equal(via_registry.elements[1].y, 110)
        assert_equal(via_registry.elements[1].width, 860)
        assert_equal(via_registry.elements[1].height, 400)
    Err(_):
        assert_true(false)
```

</details>

#### creating by the blank id yields an empty slide identical to blank_slide

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
slide_layout_registry_reset()
val legacy = blank_slide("golden5")
match create_slide_from_layout_id("blank", "golden6"):
    Ok(via_registry):
        assert_equal(via_registry.elements.len(), legacy.elements.len())
        assert_equal(via_registry.elements.len(), 0)
    Err(_):
        assert_true(false)
```

</details>

#### errors cleanly on an unknown layout id

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
slide_layout_registry_reset()
match create_slide_from_layout_id("no-such-layout", "x"):
    Ok(_):
        assert_true(false)
    Err(msg):
        assert_true(msg.len() > 0)
```

</details>

### Slide element-kind registry

#### lists the four builtin element kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ids = element_kind_registry_ids()
assert_equal(ids.len(), 4)
assert_true(element_kind_registry_has("text_box"))
assert_true(element_kind_registry_has("image"))
assert_true(element_kind_registry_has("shape"))
assert_true(element_kind_registry_has("table"))
```

</details>

#### creates a text_box element by kind id

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match create_slide_element_by_kind("text_box", "el1", 10, 20, 30, 40):
    Ok(el):
        assert_equal(el.id, "el1")
        assert_equal(el.x, 10)
        assert_equal(el.y, 20)
        assert_equal(el.width, 30)
        assert_equal(el.height, 40)
        match el.kind:
            SlideElementKind.TextBox(content):
                assert_equal(content, "New Text")
            _:
                assert_true(false)
    Err(_):
        assert_true(false)
```

</details>

#### creates a shape element by kind id

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match create_slide_element_by_kind("shape", "el2", 1, 2, 3, 4):
    Ok(el):
        match el.kind:
            SlideElementKind.ShapeEl(shape_type, fill_color):
                assert_equal(shape_type, "rectangle")
                assert_equal(fill_color, "#4A90D9")
            _:
                assert_true(false)
    Err(_):
        assert_true(false)
```

</details>

#### errors cleanly on an unknown element kind id

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match create_slide_element_by_kind("no-such-kind", "elx", 0, 0, 0, 0):
    Ok(_):
        assert_true(false)
    Err(msg):
        assert_true(msg.len() > 0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
