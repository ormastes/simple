# 27 Area Read Specification

> <details>

<!-- sdn-diagram:id=27_area_read_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=27_area_read_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

27_area_read_spec -> std
27_area_read_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=27_area_read_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 27 Area Read Specification

## Scenarios

### T32 AREA read

#### AREA lifecycle

#### creates AREA buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_has_area():
    expect("AREA not available in this T32 version").to_contain("not available")
    return
val result = t32_hw_run_cmd(client, "AREA.Create T32_HW_AREA")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("AREA.Create failed: {e}").to_equal("")
```

</details>

#### selects AREA buffer

1. t32 hw run cmd


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_has_area():
    expect("AREA not available in this T32 version").to_contain("not available")
    return
t32_hw_run_cmd(client, "AREA.Create T32_HW_AREA")
val result = t32_hw_run_cmd(client, "AREA.Select T32_HW_AREA")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("AREA.Select failed: {e}").to_equal("")
```

</details>

#### writes to AREA

1. t32 hw run cmd
2. t32 hw run cmd


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_has_area():
    expect("AREA not available in this T32 version").to_contain("not available")
    return
t32_hw_run_cmd(client, "AREA.Create T32_HW_AREA")
t32_hw_run_cmd(client, "AREA.Select T32_HW_AREA")
val result = t32_hw_run_cmd(client, "PRINT \"hw_test_output\"")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("PRINT to AREA failed: {e}").to_equal("")
```

</details>

#### AREA.view reads buffer

1. t32 hw run cmd
2. t32 hw run cmd
3. t32 hw run cmd


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_has_area():
    expect("AREA not available in this T32 version").to_contain("not available")
    return
t32_hw_run_cmd(client, "AREA.Create T32_HW_AREA")
t32_hw_run_cmd(client, "AREA.Select T32_HW_AREA")
t32_hw_run_cmd(client, "PRINT \"hw_test_output\"")
val result = t32_hw_run_cmd(client, "AREA.view")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("AREA.view failed: {e}").to_equal("")
```

</details>

#### universal output

#### PRINT works on all T32 versions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# PRINT is available in all T32 versions as a fallback
val result = t32_hw_run_cmd(client, "PRINT \"area_fallback_test\"")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("PRINT failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/27_area_read_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 AREA read

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
