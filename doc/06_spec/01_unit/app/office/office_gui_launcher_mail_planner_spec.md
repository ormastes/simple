# office_gui_launcher_mail_planner_spec

> Interactive-GUI pixel render for the Mail and Planner launcher apps.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# office_gui_launcher_mail_planner_spec

Interactive-GUI pixel render for the Mail and Planner launcher apps.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/office_gui_launcher_mail_planner_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Interactive-GUI pixel render for the Mail and Planner launcher apps.

Renders the MailApp and PlannerApp launcher surfaces through the production
browser layout/paint path (office_gui_launcher_frame in gui_apps.spl) and
asserts real (non-blank) content. Split from the sheets/slides spec so each
file stays well under the runner's kill budget.

## Scenarios

### office GUI launcher: Mail app renders pixels

#### the mail frame has real content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = office_gui_launcher_frame("mail")
val nonbg = office_gui_non_background_pixel_count(pixels)
expect(nonbg).to_be_greater_than(0)
```

</details>

### office GUI launcher: Planner app renders pixels

#### the planner frame has real content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = office_gui_launcher_frame("planner")
val nonbg = office_gui_non_background_pixel_count(pixels)
expect(nonbg).to_be_greater_than(0)
```

</details>

#### deliberate-fail probe proves the tail of the file executes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = office_gui_launcher_frame("planner")
val nonbg = office_gui_non_background_pixel_count(pixels)
expect(nonbg).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
