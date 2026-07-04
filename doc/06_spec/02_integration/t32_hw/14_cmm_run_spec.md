# 14 Cmm Run Specification

> <details>

<!-- sdn-diagram:id=14_cmm_run_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=14_cmm_run_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

14_cmm_run_spec -> std
14_cmm_run_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=14_cmm_run_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 14 Cmm Run Specification

## Scenarios

### T32 CMM run

#### inline PRACTICE

#### runs inline PRACTICE

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_run_cmd(client, "PRINT \"hello\"")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("PRINT failed: {e}").to_equal("")
```

</details>

#### AREA.Create succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_has_area():
    expect("AREA not available in this T32 version").to_contain("not available")
    return
val result = t32_hw_run_cmd(client, "AREA.Create T32_HW_TEST")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("AREA.Create failed: {e}").to_equal("")
```

</details>

#### AREA.Select succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_has_area():
    expect("AREA not available in this T32 version").to_contain("not available")
    return
val result = t32_hw_run_cmd(client, "AREA.Select T32_HW_TEST")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("AREA.Select failed: {e}").to_equal("")
```

</details>

#### runs multiple PRINT commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# PRINT works on all T32 versions including old 2013 builds
val r1 = t32_hw_run_cmd(client, "PRINT \"test_line_1\"")
val r2 = t32_hw_run_cmd(client, "PRINT \"test_line_2\"")
match r1:
    Ok(_): expect("print1 ok").to_contain("ok")
    Err(e): expect("PRINT 1 failed: {e}").to_equal("")
match r2:
    Ok(_): expect("print2 ok").to_contain("ok")
    Err(e): expect("PRINT 2 failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/14_cmm_run_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 CMM run

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
