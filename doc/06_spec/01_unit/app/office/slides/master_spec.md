# master_spec

> Slide master + placeholder-inheritance spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# master_spec

Slide master + placeholder-inheritance spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/slides/master_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Slide master + placeholder-inheritance spec.

Verifies the slide master model in `app.office.slides.master`: placeholders
defined on a master carry position/size/font that every slide inherits; a
slide supplies only content (title/body/page number); when content is
missing the master's default_text is used; and the master renders to a
compact PowerPoint-like `<p:sldMaster>` XML fragment.

## Scenarios

### slide master: placeholder inheritance

#### inherits position and font from the master while using the slide's title/body/page

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var master = master_new("Default")
master = master_add_placeholder(master, placeholder_new("title", 0, 0, 720, 80, 44, "Title"))
master = master_add_placeholder(master, placeholder_new("body", 0, 100, 720, 400, 24, "Body"))
master = master_add_placeholder(master, placeholder_new("pageno", 680, 520, 40, 20, 12, "#"))
val lines = apply_master(master, "My Talk", "Point one", 3)

val title_line = lines[0]
expect(title_line).to_contain("My Talk")
expect(title_line).to_contain("44pt")
expect(title_line).to_contain("@0,0")

val body_line = lines[1]
expect(body_line).to_contain("Point one")
expect(body_line).to_contain("24pt")

val pageno_line = lines[2]
expect(pageno_line).to_contain("3")
```

</details>

#### falls back to the master's default_text when the slide's body is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var master = master_new("Default")
master = master_add_placeholder(master, placeholder_new("title", 0, 0, 720, 80, 44, "Title"))
master = master_add_placeholder(master, placeholder_new("body", 0, 100, 720, 400, 24, "Body"))
master = master_add_placeholder(master, placeholder_new("pageno", 680, 520, 40, 20, 12, "#"))
val lines = apply_master(master, "My Talk", "", 3)
val body_line = lines[1]
expect(body_line).to_contain("Body")
```

</details>

#### counts the placeholders defined on the master

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var master = master_new("Default")
master = master_add_placeholder(master, placeholder_new("title", 0, 0, 720, 80, 44, "Title"))
master = master_add_placeholder(master, placeholder_new("body", 0, 100, 720, 400, 24, "Body"))
master = master_add_placeholder(master, placeholder_new("pageno", 680, 520, 40, 20, 12, "#"))
expect(master_placeholder_count(master)).to_equal(3)
```

</details>

### slide master: XML rendering

#### renders a <p:sldMaster> fragment containing all three placeholder kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var master = master_new("Default")
master = master_add_placeholder(master, placeholder_new("title", 0, 0, 720, 80, 44, "Title"))
master = master_add_placeholder(master, placeholder_new("body", 0, 100, 720, 400, 24, "Body"))
master = master_add_placeholder(master, placeholder_new("pageno", 680, 520, 40, 20, 12, "#"))
val xml = master_to_xml(master)
expect(xml).to_contain("<p:sldMaster")
expect(xml).to_contain("type=\"title\"")
expect(xml).to_contain("type=\"body\"")
expect(xml).to_contain("type=\"pageno\"")
```

</details>

### deliberate-fail probe (fixed to green)

#### has exactly three placeholders

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var master = master_new("Default")
master = master_add_placeholder(master, placeholder_new("title", 0, 0, 720, 80, 44, "Title"))
master = master_add_placeholder(master, placeholder_new("body", 0, 100, 720, 400, 24, "Body"))
master = master_add_placeholder(master, placeholder_new("pageno", 680, 520, 40, 20, 12, "#"))
expect(master_placeholder_count(master)).to_equal(3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
