# @manual: primary

> <details>

<!-- sdn-diagram:id=serial_mcp_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=serial_mcp_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

serial_mcp_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=serial_mcp_numeric_guard_spec.arch hash=sha256:auto
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

### serial mcp numeric guard

#### defaults malformed integer arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/serial_mcp/tools.spl") ?? ""

expect(source).to_contain("val n = s.to_int() ?? default_val")
expect(source.contains("val n = s.to_int()\n")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/serial_mcp/serial_mcp_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify serial mcp numeric argument guard behavior at runtime — the
production argument parser must fall back to the documented default whenever a
client supplies a malformed integer argument.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
Troubleshooting: a red scenario here means the pinned contract changed —
check verification guidance in the linked design docs before editing oracles.
# @manual: primary
REQ-APP-SERIALMCP-001
doc/01_research/local/REQ-APP-SERIALMCP-001.md
doc/03_plan/sys_test/REQ-APP-SERIALMCP-001.md
doc/04_architecture/REQ-APP-SERIALMCP-001.md
doc/05_design/REQ-APP-SERIALMCP-001.md

Tests covering:
- serial mcp numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
