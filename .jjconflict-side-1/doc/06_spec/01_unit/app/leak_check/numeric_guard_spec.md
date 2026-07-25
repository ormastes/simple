# Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Numeric Guard Specification

## Scenarios

### leak check numeric guard

#### keeps malformed numeric CLI and parser values from flowing as nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = rt_file_read_text("src/compiler/90.tools/leak_check/config.spl") ?? ""
val parser = rt_file_read_text("src/compiler/90.tools/leak_check/parser.spl") ?? ""
val internal_runner = rt_file_read_text("src/compiler/90.tools/leak_check/internal_runner.spl") ?? ""

expect(config).to_contain("cfg.gc_leak_window = window_str.to_int() ?? cfg.gc_leak_window")
expect(config).to_contain("cfg.timeout_seconds = timeout_str.to_int() ?? cfg.timeout_seconds")
expect(parser).to_contain("return cleaned.to_int() ?? 0")
expect(parser).to_contain("return num_str.to_int() ?? 0")
expect(internal_runner).to_contain("return num_str.to_int() ?? -1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/leak_check/numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- leak check numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
