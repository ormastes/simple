# Session Int Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=session_int_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=session_int_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

session_int_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=session_int_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Session Int Numeric Guard Specification

## Scenarios

### web framework session integer numeric guard

#### returns nil for malformed typed integer session values

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/nogc_sync_mut/web_framework/session.spl") ?? ""

expect(source).to_contain("fn _parse_session_int(raw: text) -> i64?:")
expect(source).to_contain("if ch < \"0\" or ch > \"9\":")
expect(source).to_contain("val value = self._parse_session_int(s[2:])")
expect(source).to_contain("if value == nil:")
expect(source.contains("val value = s[2:].to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/web_framework/session_int_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- web framework session integer numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
