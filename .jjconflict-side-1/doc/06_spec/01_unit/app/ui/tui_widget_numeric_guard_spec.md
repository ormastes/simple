# @manual: primary

> <details>

<!-- sdn-diagram:id=tui_widget_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tui_widget_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tui_widget_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tui_widget_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

## Scenarios

### tui widget numeric guards

#### guards widget property integer parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/ui.render/tui_widgets_part1.spl") ?? ""

expect(source).to_contain("fn tui_int_or(value: text, default_value: i64) -> i64")
expect(source).to_contain("tui_int_or(sel_str, -1)")
expect(source).to_contain("tui_int_or(value_str, 0)")
expect(source).to_contain("tui_int_or(active_idx_str, 0)")
expect(source).to_contain("tui_int_or(offset_str, 0)")
expect(source).to_contain("trimmed.to_int() ?? default_value")
expect(source.contains("sel_str.to_int()")).to_equal(false)
expect(source.contains("active_idx_str.to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/tui_widget_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify tui widget numeric guards.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
Troubleshooting: a red scenario here means the pinned contract changed —
check verification guidance in the linked design docs before editing oracles.
# @manual: primary
REQ-APP-UI-001
doc/01_research/local/REQ-APP-UI-001.md
doc/03_plan/sys_test/REQ-APP-UI-001.md
doc/04_architecture/REQ-APP-UI-001.md
doc/05_design/REQ-APP-UI-001.md

Tests covering:
- tui widget numeric guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
