# @manual: primary

> <details>

<!-- sdn-diagram:id=dynamic_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dynamic_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dynamic_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dynamic_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

## Scenarios

### dynamic stats numeric guard

#### guards shell count parsing with one fallback helper

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/stats/dynamic.spl") ?? ""

expect(source).to_contain("fn parse_count(output: text) -> i64:")
expect(source).to_contain("output.to_int() ?? 0")
expect(source).to_contain("parse_count(run_cmd(cmd))")
expect(source.contains("run_cmd(cmd).to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/stats/dynamic_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify dynamic stats shell-count parsing guard at runtime — the
production count parser must coerce malformed shell output to 0 instead of
crashing or trusting raw text.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
Troubleshooting: a red scenario here means the pinned contract changed —
check verification guidance in the linked design docs before editing oracles.
# @manual: primary
REQ-APP-STATS-001
doc/01_research/local/REQ-APP-STATS-001.md
doc/03_plan/sys_test/REQ-APP-STATS-001.md
doc/04_architecture/REQ-APP-STATS-001.md
doc/05_design/REQ-APP-STATS-001.md

Tests covering:
- dynamic stats numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
