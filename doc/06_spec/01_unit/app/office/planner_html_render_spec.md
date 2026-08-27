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
| Updated | 2026-08-26 |
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

- shows the task title


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows the task title")
val html = render_task_html(new_task("t1", "Design mockups"))
expect(html).to_contain("Design mockups")
```

</details>

#### HTML-escapes a <b> tag embedded in the task title

- HTML-escapes a <b> tag embedded in the task title


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("HTML-escapes a <b> tag embedded in the task title")
val html = render_task_html(new_task("t2", "<b>Bold</b> Task"))
expect(html).to_contain("&lt;b&gt;Bold&lt;/b&gt; Task")
expect(html.contains("<b>Bold</b>")).to_be(false)
```

</details>

#### wraps the card in a styled div

- wraps the card in a styled div


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps the card in a styled div")
val html = render_task_html(new_task("t3", "Write tests"))
expect(html).to_start_with("<div class=\"task-card\"")
expect(html).to_end_with("</div>")
```

</details>

#### shows the status badge

- shows the status badge


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows the status badge")
val html = render_task_html(new_task("t4", "Todo task"))
expect(html).to_contain("class=\"status-badge\"")
expect(html).to_contain(">Todo</span>")
```

</details>

### planner HTML render: kanban board

#### renders all board lanes

- renders all board lanes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders all board lanes")
val html = render_board_html(_demo_app())
expect(html).to_contain(">Todo (")
expect(html).to_contain(">In Progress (")
expect(html).to_contain(">Done (")
```

</details>

#### contains all demo tasks

- contains all demo tasks


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains all demo tasks")
val html = render_board_html(_demo_app())
expect(html).to_contain("Design mockups")
expect(html).to_contain("Build API")
expect(html).to_contain("Ship release")
```

</details>

#### wraps the board in a flex row container

- wraps the board in a flex row container


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps the board in a flex row container")
val html = render_board_html(_demo_app())
expect(html).to_start_with("<div class=\"kanban-board\"")
expect(html).to_contain("display: flex;")
```

</details>

#### renders an empty board with lanes and zero counts

- renders an empty board with lanes and zero counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders an empty board with lanes and zero counts")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a80182bd6bee84bdaa843704d0c6d6bcf122e026659f07c53cc1e4cb155d0bb2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a80182bd6bee84bdaa843704d0c6d6bcf122e026659f07c53cc1e4cb155d0bb2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a80182bd6bee84bdaa843704d0c6d6bcf122e026659f07c53cc1e4cb155d0bb2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/planner_html_render_spec.spl
mirror: doc/06_spec/01_unit/app/office/planner_html_render_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/planner_html_render_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/planner_html_render_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/planner_html_render_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows the task title' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/planner_html_render_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'HTML-escapes a <b> tag embedded in the task title' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/planner_html_render_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wraps the card in a styled div' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
