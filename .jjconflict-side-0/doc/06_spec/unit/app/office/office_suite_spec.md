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
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office([])).to_equal(0)
```

</details>

#### loads word

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["word"])).to_equal(0)
```

</details>

#### loads sheets

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["sheets"])).to_equal(0)
```

</details>

#### loads slides

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["slides"])).to_equal(0)
```

</details>

#### loads mail

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["mail"])).to_equal(0)
```

</details>

#### loads planner

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["planner"])).to_equal(0)
```

</details>

#### rejects unknown app

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["unknown"])).to_equal(1)
```

</details>

### Office UI

#### builds launcher ui

1. RecentFile
   - Expected: ui.root_id equals `root`


<details>
<summary>Executable SPipe</summary>

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

#### builds word ui

<details>
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app = PlannerApp.new()
val ui = app.build_ui()
expect(ui.root_id).to_equal("root")
```

</details>

### Office Hardening

#### adds slides image element without fake asset path

1. var app = SlidesApp new

2. app handle event
   - Expected: slide.elements.len() equals `2`

3. SlideElementKind ImageEl
   - Expected: src equals ``
   - Expected: alt equals `Image Frame`
   - Expected: false is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var app = SlidesApp.new()
app.handle_event(UIEvent.Action(name: "add_image"))
val slide = current_slide(app.presentation)
expect(slide.elements.len()).to_equal(2)
match slide.elements[slide.elements.len() - 1].kind:
    SlideElementKind.ImageEl(src: src, alt: alt):
        expect(src).to_equal("")
        expect(alt).to_equal("Image Frame")
    _:
        expect(false).to_equal(true)
```

</details>

#### formats date values honestly in sheets

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val formatted = apply_cell_format(366.0, "date")
expect(formatted).to_equal("1971-01-02")
```

</details>

#### replaces the first office search match

<details>
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

