# Tmp Office Hardening Probe Specification

## Scenarios

### Office hardening probe

#### checks office hardening expectations

1. var app = SlidesApp new

2. app handle event
   - Expected: slide.elements.len() equals `2`

3. SlideElementKind ImageEl
   - Expected: src equals ``
   - Expected: alt equals `Image Frame`
   - Expected: false is true
   - Expected: apply_cell_format(366.0, "date") equals `1971-01-02`
   - Expected: replace_first("draft draft", "draft", "final", 0, options) equals `final draft`
   - Expected: priority_name(task.priority) equals `None`
   - Expected: priority_icon(task.priority) equals `-`


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
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
expect(apply_cell_format(366.0, "date")).to_equal("1971-01-02")
val options = default_search_options()
expect(replace_first("draft draft", "draft", "final", 0, options)).to_equal("final draft")
val task = new_task("task_0", "Backlog")
expect(priority_name(task.priority)).to_equal("None")
expect(priority_icon(task.priority)).to_equal("-")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/tmp_office_hardening_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Office hardening probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

