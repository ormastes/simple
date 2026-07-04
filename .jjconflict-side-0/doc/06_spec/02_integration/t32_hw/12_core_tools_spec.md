# 12 Core Tools Specification

> <details>

<!-- sdn-diagram:id=12_core_tools_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=12_core_tools_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

12_core_tools_spec -> std
12_core_tools_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=12_core_tools_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 12 Core Tools Specification

## Scenarios

### T32 core tools

#### CPU and state queries

#### queries CPU type

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_run_cmd(client, "PRINT CPU()")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("CPU query failed: {e}").to_equal("")
```

</details>

#### queries system state

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_eval(client, "STATE.RUN()")
match result:
    Ok(_): expect("eval ok").to_contain("ok")
    Err(e): expect("STATE.RUN failed: {e}").to_equal("")
```

</details>

#### queries debug mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_eval(client, "DEBUGMODE()")
match result:
    Ok(_): expect("eval ok").to_contain("ok")
    Err(e): expect("DEBUGMODE failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/12_core_tools_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 core tools

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
