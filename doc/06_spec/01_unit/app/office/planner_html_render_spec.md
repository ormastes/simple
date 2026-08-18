# planner_html_render_spec

> Planner HTML render spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# planner_html_render_spec

Planner HTML render spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/planner_html_render_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Planner HTML render spec.

Verifies that `render_task_html` and `render_board_html` render the Planner
surface as a Trello-like kanban board — one flex column per status lane, each
holding styled task cards — as a pure model -> HTML transform with inline CSS
only.

All assertions are over the produced HTML string, so they run on the test
runner without the f64/i32 toolchain fragility.

## Scenarios

### planner HTML render: task card

#### shows the task title

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_task_html(new_task("t1", "Design mockups"))
expect(html).to_contain("Design mockups")
```

</details>

#### HTML-escapes a <b> tag embedded in the task title

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_task_html(new_task("t2", "<b>Bold</b> Task"))
expect(html).to_contain("&lt;b&gt;Bold&lt;/b&gt; Task")
expect(html.contains("<b>Bold</b>")).to_be(false)
```

</details>

#### wraps the card in a styled div

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_task_html(new_task("t3", "Write tests"))
expect(html).to_start_with("<div class=\"task-card\"")
expect(html).to_end_with("</div>")
```

</details>

#### shows the status badge

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_task_html(new_task("t4", "Todo task"))
expect(html).to_contain("class=\"status-badge\"")
expect(html).to_contain(">Todo</span>")
```

</details>

### planner HTML render: kanban board

#### renders all board lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_board_html(_demo_app())
expect(html).to_contain(">Todo (")
expect(html).to_contain(">In Progress (")
expect(html).to_contain(">Done (")
```

</details>

#### contains all demo tasks

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_board_html(_demo_app())
expect(html).to_contain("Design mockups")
expect(html).to_contain("Build API")
expect(html).to_contain("Ship release")
```

</details>

#### wraps the board in a flex row container

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_board_html(_demo_app())
expect(html).to_start_with("<div class=\"kanban-board\"")
expect(html).to_contain("display: flex;")
```

</details>

#### renders an empty board with lanes and zero counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app = PlannerApp.new()
val html = render_board_html(app)
expect(html).to_contain(">Todo (0)</div>")
expect(html).to_contain(">In Progress (0/5)</div>")
expect(html).to_contain(">Done (0)</div>")
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
