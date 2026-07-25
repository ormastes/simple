# 18 Window Open Capture Specification

> <details>

<!-- sdn-diagram:id=18_window_open_capture_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=18_window_open_capture_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

18_window_open_capture_spec -> std
18_window_open_capture_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=18_window_open_capture_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 18 Window Open Capture Specification

## Scenarios

### T32 window open capture

#### register window capture

#### opens Register window

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_run_cmd(client, "Register /SpotLight")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("Register /SpotLight failed: {e}").to_equal("")
```

</details>

#### captures Register text

1. Ok
2. Err
   - Expected: "Register /All failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_run_cmd(client, "Register /All")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("Register /All failed: {e}").to_equal("")
```

</details>

#### register read API

#### read_all_registers returns data

1. Ok
2. Err
   - Expected: "read_all_registers failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = client.read_all_registers()
match result:
    Ok(regs):
        expect(regs.len()).to_be_greater_than(0)
    Err(e):
        expect("read_all_registers failed: {e}").to_equal("")
```

</details>

#### read PC register

1. Ok
2. Err
   - Expected: "read_register PC failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = client.read_register("PC")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("read_register PC failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/18_window_open_capture_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 window open capture

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
