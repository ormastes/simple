# 17 Window List Describe Specification

> <details>

<!-- sdn-diagram:id=17_window_list_describe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=17_window_list_describe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

17_window_list_describe_spec -> std
17_window_list_describe_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=17_window_list_describe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 17 Window List Describe Specification

## Scenarios

### T32 window list describe

#### window operations

#### window open Register

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_run_cmd(client, "Register")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("Register window failed: {e}").to_equal("")
```

</details>

#### window open Data.dump

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_run_cmd(client, "Data.dump")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("Data.dump window failed: {e}").to_equal("")
```

</details>

#### WinPOS query works

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_run_cmd(client, "WinPOS")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("WinPOS failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/17_window_list_describe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 window list describe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
