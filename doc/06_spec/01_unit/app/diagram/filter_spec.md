# Filter Specification

> <details>

<!-- sdn-diagram:id=filter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=filter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

filter_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=filter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Filter Specification

## Scenarios

### Filter

#### keeps diagram event parsing and generation entrypoints available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/diagram/main.spl") ?? ""

expect(source).to_contain("struct ProfileEvent")
expect(source).to_contain("fn parse_profile_events(content: text) -> [ProfileEvent]")
expect(source).to_contain("fn generate_sequence_diagram(events: [ProfileEvent], include_timing: bool, include_args: bool, include_returns: bool) -> text")
expect(source).to_contain("fn generate_class_diagram(events: [ProfileEvent]) -> text")
expect(source).to_contain("fn generate_arch_diagram(events: [ProfileEvent]) -> text")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/diagram/filter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Filter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
