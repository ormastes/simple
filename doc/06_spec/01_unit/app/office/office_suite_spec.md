# office_suite_spec

> Office suite unit specification.

<!-- sdn-diagram:id=office_suite_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=office_suite_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

office_suite_spec -> std
office_suite_spec -> app
office_suite_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=office_suite_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# office_suite_spec

Office suite unit specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/office_suite_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Office suite unit specification.
Exercises the canonical office app entrypoint, launcher, and app-specific UI construction paths.

## Scenarios

### Office CLI

#### defaults to launcher

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office([])).to_equal(0)
```

</details>

#### loads word

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["word"])).to_equal(0)
```

</details>

#### loads sheets

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["sheets"])).to_equal(0)
```

</details>

#### loads slides

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["slides"])).to_equal(0)
```

</details>

#### loads mail

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["mail"])).to_equal(0)
```

</details>

#### loads planner

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["planner"])).to_equal(0)
```

</details>

#### loads counter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["counter"])).to_equal(0)
```

</details>

#### applies markdown edit commands when expected source matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["md-edit", "1", "second", "changed", "first\\nsecond"])).to_equal(0)
```

</details>

#### rejects markdown edit commands when actual source differs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["md-edit", "1", "expected", "changed", "first\\nactual"])).to_equal(2)
```

</details>

#### rejects markdown edit commands with trailing arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["md-edit", "1", "second", "changed", "first\\nsecond", "extra"])).to_equal(1)
```

</details>

#### rejects markdown edit commands with malformed line tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["md-edit", "abc", "first", "changed", "first\\nsecond"])).to_equal(2)
expect(run_office(["md-edit", "-1", "first", "changed", "first\\nsecond"])).to_equal(2)
expect(run_office(["md-edit", "", "first", "changed", "first\\nsecond"])).to_equal(2)
expect(run_office(["md-edit", "9999999999", "first", "changed", "first\\nsecond"])).to_equal(2)
```

</details>

#### applies sheet edit commands when expected cell display matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["sheet-edit", "A1", "old", "new", "A1=old;B1=2"])).to_equal(0)
```

</details>

#### rejects sheet edit commands when actual cell display differs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["sheet-edit", "A1", "expected", "new", "A1=actual;B1=2"])).to_equal(2)
```

</details>

#### rejects sheet edit commands with malformed target references

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["sheet-edit", "not-a-ref", "", "new", "A1=old"])).to_equal(2)
```

</details>

#### rejects sheet edit commands for missing target cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["sheet-edit", "A1", "", "new", ""])).to_equal(2)
```

</details>

#### rejects sheet edit commands with malformed source entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["sheet-edit", "A1", "old", "new", "A1old;B1=2"])).to_equal(2)
```

</details>

#### rejects sheet edit commands with malformed source references

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["sheet-edit", "A1", "old", "new", "A1=old;not-a-ref=2"])).to_equal(2)
```

</details>

#### rejects sheet edit commands with trailing arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["sheet-edit", "A1", "old", "new", "A1=old", "extra"])).to_equal(1)
```

</details>

#### applies slide edit commands when expected text matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["slide-edit", "title", "old", "new", "title=old;body=second"])).to_equal(0)
```

</details>

#### rejects slide edit commands when actual text differs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["slide-edit", "title", "expected", "new", "title=actual;body=second"])).to_equal(2)
```

</details>

#### rejects slide edit commands for missing elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["slide-edit", "title", "", "new", "body=second"])).to_equal(2)
```

</details>

#### rejects slide edit commands with malformed source entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["slide-edit", "title", "old", "new", "titleold;body=second"])).to_equal(2)
```

</details>

#### rejects slide edit commands with missing source ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["slide-edit", "title", "old", "new", "=old"])).to_equal(2)
```

</details>

#### rejects slide edit commands with trailing arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["slide-edit", "title", "old", "new", "title=old", "extra"])).to_equal(1)
```

</details>

#### rejects unknown app

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["unknown"])).to_equal(1)
```

</details>

### Office UI

#### builds launcher ui

- RecentFile
   - Expected: ui.root_id equals `root`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val recent = [
    RecentFile(path: "/tmp/test.sdoc", app_name: "word", title: "Test Doc", timestamp: "2026-03-25")
]
val ui = build_launcher_ui(recent)
expect(ui.root_id).to_equal("root")
```

</details>

#### keeps launcher actions allowlisted and resolves counter actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(launcher_action_allowlist().len()).to_equal(6)
expect(launcher_open_action("word")).to_equal("open_word")
expect(is_valid_launcher_action("open_word")).to_be(true)
expect(is_valid_launcher_action("open_counter")).to_be(true)
val slides = launcher_action_to_component("open_slides")
expect(slides.is_some()).to_be(true)
expect(slides.unwrap()).to_equal("slides")
val counter = launcher_action_to_component("open_counter")
expect(counter.is_some()).to_be(true)
expect(counter.unwrap()).to_equal("counter")
```

</details>

#### builds word ui

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app = WordApp.new()
val ui = app.build_ui()
expect(ui.root_id).to_equal("word_root")
expect(app.word_count()).to_equal(0)
```

</details>

#### builds sheets ui

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app = SheetsApp.new()
val ui = app.build_ui()
expect(ui.root_id).to_equal("root")
```

</details>

#### builds slides ui

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app = SlidesApp.new()
val ui = app.build_ui()
expect(ui.root_id).to_equal("root")
```

</details>

#### builds mail ui with sample data

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app = MailApp.new()
val ui = app.build_ui()
expect(ui.root_id).to_equal("root")
expect(app.emails.len()).to_equal(5)
expect(app.unread_count()).to_equal(2)
```

</details>

#### builds planner ui

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app = PlannerApp.new()
val ui = app.build_ui()
expect(ui.root_id).to_equal("root")
```

</details>

#### builds counter ui and applies deterministic transitions

- var app = CounterApp new
   - Expected: ui.root_id equals `root`
   - Expected: inc.value equals `1`
   - Expected: inc.status equals `incremented`
- app handle event
   - Expected: app.value equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var app = CounterApp.new()
val ui = app.build_ui()
expect(ui.root_id).to_equal("root")
val inc = counter_apply_action(app.value, "counter_increment")
expect(inc.value).to_equal(1)
expect(inc.status).to_equal("incremented")
app.handle_event(UIEvent.Action(name: "counter_increment"))
expect(app.value).to_equal(1)
```

</details>

### Office Hardening

#### adds slides image element without fake asset path

- var app = SlidesApp new
- app handle event
   - Expected: slide.elements.len() equals `2`
- SlideElementKind ImageEl
   - Expected: image_src equals ``
   - Expected: image_alt equals `Image Frame`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var app = SlidesApp.new()
app.handle_event(UIEvent.Action(name: "add_image"))
val slide = current_slide(app.presentation)
expect(slide.elements.len()).to_equal(2)
var image_src = "<not-image>"
var image_alt = "<not-image>"
match slide.elements[slide.elements.len() - 1].kind:
    SlideElementKind.ImageEl(src: src, alt: alt):
        image_src = src
        image_alt = alt
    _:
        image_src = "<not-image>"
        image_alt = "<not-image>"
expect(image_src).to_equal("")
expect(image_alt).to_equal("Image Frame")
```

</details>

#### formats date values honestly in sheets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val formatted = apply_cell_format(366.0, "date")
expect(formatted).to_equal("1971-01-02")
```

</details>

#### updates sheets cells only when expected display matches

- sheet set value
   - Expected: result.reason equals `updated`
   - Expected: result.diff equals `@@ cell A1 @@\n- old\n+ new`
   - Expected: cell_display_text(sheet.get_cell("A1")) equals `new`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = Sheet.new("Checked")
sheet.set_value("A1", "old")
val result = sheet.update_cell_checked("A1", "old", "new")
expect(result.accepted).to_be(true)
expect(result.reason).to_equal("updated")
expect(result.diff).to_equal("@@ cell A1 @@\n- old\n+ new")
expect(cell_display_text(sheet.get_cell("A1"))).to_equal("new")
```

</details>

#### rejects stale sheet cell updates without mutating

- sheet set value
   - Expected: result.reason equals `stale-cell`
   - Expected: result.diff equals `@@ cell A1 @@\nexpected: expected\nactual: actual\nrejected: new`
   - Expected: cell_display_text(sheet.get_cell("A1")) equals `actual`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = Sheet.new("Checked")
sheet.set_value("A1", "actual")
val result = sheet.update_cell_checked("A1", "expected", "new")
expect(result.accepted).to_be(false)
expect(result.reason).to_equal("stale-cell")
expect(result.diff).to_equal("@@ cell A1 @@\nexpected: expected\nactual: actual\nrejected: new")
expect(cell_display_text(sheet.get_cell("A1"))).to_equal("actual")
```

</details>

#### rejects malformed sheet cell references without mutating

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = Sheet.new("Checked")
val result = sheet.update_cell_checked("not-a-ref", "", "new")
expect(result.accepted).to_be(false)
expect(result.reason).to_equal("invalid-cell-ref")
expect(result.actual_value).to_equal("<invalid-ref>")
expect(sheet.cell_count()).to_equal(0)
```

</details>

#### rejects missing sheet cells without creating them

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheet = Sheet.new("Checked")
val result = sheet.update_cell_checked("A1", "", "new")
expect(result.accepted).to_be(false)
expect(result.reason).to_equal("missing-cell")
expect(result.actual_value).to_equal("<missing-cell>")
expect(sheet.cell_count()).to_equal(0)
```

</details>

#### updates slide text elements only when expected text matches

- SlideElementKind TextBox
   - Expected: actual equals `new`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slide = add_text_box(blank_slide("checked"), "title", "old", 40, 40, 840, 60)
val result = slide_update_text_checked(slide, "title", "old", "new")
expect(result.accepted).to_be(true)
expect(result.reason).to_equal("updated")
expect(result.diff).to_equal("@@ slide element title @@\n- old\n+ new")
var actual = "<missing>"
match result.slide.elements[0].kind:
    SlideElementKind.TextBox(content: content):
        actual = content
    _:
        actual = "<not-text>"
expect(actual).to_equal("new")
```

</details>

#### rejects stale slide text updates without mutating

- SlideElementKind TextBox
   - Expected: actual equals `actual`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slide = add_text_box(blank_slide("checked"), "title", "actual", 40, 40, 840, 60)
val result = slide_update_text_checked(slide, "title", "expected", "new")
expect(result.accepted).to_be(false)
expect(result.reason).to_equal("stale-slide-element")
expect(result.diff).to_equal("@@ slide element title @@\nexpected: expected\nactual: actual\nrejected: new")
var actual = "<missing>"
match result.slide.elements[0].kind:
    SlideElementKind.TextBox(content: content):
        actual = content
    _:
        actual = "<not-text>"
expect(actual).to_equal("actual")
```

</details>

#### rejects missing slide text elements without mutating

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slide = blank_slide("checked")
val result = slide_update_text_checked(slide, "title", "", "new")
expect(result.accepted).to_be(false)
expect(result.reason).to_equal("missing-element")
expect(result.actual_value).to_equal("<missing-element>")
expect(result.slide.elements.len()).to_equal(0)
```

</details>

#### replaces the first office search match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_search_options()
val result = replace_first("draft draft", "draft", "final", 0, options)
expect(result).to_equal("final draft")
```

</details>

#### uses a stable unset planner priority without command warnings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = new_task("task_0", "Backlog")
expect(priority_name(task.priority)).to_equal("None")
expect(priority_icon(task.priority)).to_equal("-")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
