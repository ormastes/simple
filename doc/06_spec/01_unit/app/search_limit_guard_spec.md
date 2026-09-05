# Search Limit Guard Specification

> <details>

<!-- sdn-diagram:id=search_limit_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=search_limit_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

search_limit_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=search_limit_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Search Limit Guard Specification

## Scenarios

### search limit guard

#### guards malformed limit parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/search/main.spl") ?? ""

expect(source).to_contain("fn parse_limit_or_default(value: text) -> i64")
expect(source).to_contain("for ch in trimmed:")
expect(source).to_contain("if ch < \"0\" or ch > \"9\":")
expect(source).to_contain("if parsed <= 0:")
expect(source).to_contain("return 20")
expect(source).to_contain("limit = parse_limit_or_default(arg[8:])")
expect(source.contains("limit = arg[8:].to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/search_limit_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- search limit guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
