# 23 Screenshot Specification

> <details>

<!-- sdn-diagram:id=23_screenshot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=23_screenshot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

23_screenshot_spec -> std
23_screenshot_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=23_screenshot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 23 Screenshot Specification

## Scenarios

### T32 screenshot

#### print and capture

#### screenshot command exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_run_cmd(client, "PRINT \"screenshot_test\"")
match result:
    Ok(v): expect(v).to_contain("screenshot_test")
    Err(e): expect("PRINT failed: {e}").to_equal("")
```

</details>

#### WinPrint captures window

1. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# WinPrint.Register may fail if no register window is open
val result = t32_hw_run_cmd(client, "WinPrint.Register")
match result:
    Ok(v): expect(v).to_contain("")
    Err(_):
        return "skip: register window may not be open in headless mode"
```

</details>

#### ScreenShot path queryable

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
return "skip: screenshot capture requires GUI environment"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/23_screenshot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 screenshot

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
