# @manual: primary

> <details>

<!-- sdn-diagram:id=tree_depth_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tree_depth_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tree_depth_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tree_depth_numeric_guard_spec.arch hash=sha256:auto
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

### tree depth numeric guard

#### defaults malformed depth values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/tree/main.spl") ?? ""

expect(source).to_contain("fn parse_tree_depth_or_default(value: text, default_value: i64) -> i64")
expect(source).to_contain("return trimmed.to_int() ?? default_value")
expect(source.contains("return trimmed.to_int()\n")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tree/tree_depth_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify tree depth numeric guard.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
Troubleshooting: a red scenario here means the pinned contract changed —
check verification guidance in the linked design docs before editing oracles.
# @manual: primary
REQ-APP-TREE-001
doc/01_research/local/REQ-APP-TREE-001.md
doc/03_plan/sys_test/REQ-APP-TREE-001.md
doc/04_architecture/REQ-APP-TREE-001.md
doc/05_design/REQ-APP-TREE-001.md

Tests covering:
- tree depth numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
