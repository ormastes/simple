# Standalone Content Length Guard Specification

> <details>

<!-- sdn-diagram:id=standalone_content_length_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=standalone_content_length_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

standalone_content_length_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=standalone_content_length_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Standalone Content Length Guard Specification

## Scenarios

### standalone content length guard

#### defaults malformed content length parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/ui.standalone/bootstrap.spl") ?? ""

expect(source).to_contain("content_length = len_str.trim().to_int() ?? 0")
expect(source.contains("content_length = len_str.trim().to_int()\n")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/standalone_content_length_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- standalone content length guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
