# Repl Multiline System Specification

> <details>

<!-- sdn-diagram:id=repl_multiline_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=repl_multiline_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

repl_multiline_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=repl_multiline_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Repl Multiline System Specification

## Scenarios

### REPL Multi-line Input

<details>
<summary>Advanced: should handle multi-line function definitions</summary>

#### should handle multi-line function definitions _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input_text = "fn add(a: i64, b: i64) -> i64:\n    a + b\n\nprint add(3, 4)\n:quit\n"
val output = run_repl(input_text)
expect(output).to_contain("7")
```

</details>


</details>

<details>
<summary>Advanced: should handle multi-line if/else</summary>

#### should handle multi-line if/else _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input_text = "val x = 10\nif x > 5:\n    print \"big\"\n\n:quit\n"
val output = run_repl(input_text)
expect(output).to_contain("big")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/repl/repl_multiline_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- REPL Multi-line Input

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 2 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
