# Jj Log Limit Guard Specification

> <details>

<!-- sdn-diagram:id=jj_log_limit_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=jj_log_limit_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

jj_log_limit_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=jj_log_limit_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jj Log Limit Guard Specification

## Scenarios

### jj log limit guard

#### guards malformed limit values

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/jj/log.spl") ?? ""

expect(source).to_contain("fn parse_log_limit_or_default(value: text, default_value: i64) -> i64")
expect(source).to_contain("limit = parse_log_limit_or_default(args[i], limit)")
expect(source).to_contain("limit = parse_log_limit_or_default(arg[2:], limit)")
expect(source).to_contain("limit = parse_log_limit_or_default(arg[8:], limit)")
expect(source.contains("limit = args[i].to_int()")).to_equal(false)
expect(source.contains("limit = arg[2:].to_int()")).to_equal(false)
expect(source.contains("limit = arg[8:].to_int()")).to_equal(false)
expect(source.contains("rt_process_run")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/jj_log_limit_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- jj log limit guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
