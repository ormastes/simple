# 28 Setup Headless Specification

> <details>

<!-- sdn-diagram:id=28_setup_headless_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=28_setup_headless_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

28_setup_headless_spec -> std
28_setup_headless_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=28_setup_headless_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 28 Setup Headless Specification

## Scenarios

### T32 setup headless

#### headless operations

#### SYStem.Up in headless mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_run_cmd(client, "SYStem.Up")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("SYStem.Up failed: {e}").to_equal("")
```

</details>

#### AREA operations work headless

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_has_area():
    expect("AREA not available in this T32 version").to_contain("not available")
    return
val create = t32_hw_run_cmd(client, "AREA.Create T32_HEADLESS")
match create:
    Ok(_): expect("create ok").to_contain("ok")
    Err(e): expect("AREA.Create failed: {e}").to_equal("")
val select = t32_hw_run_cmd(client, "AREA.Select T32_HEADLESS")
match select:
    Ok(_): expect("select ok").to_contain("ok")
    Err(e): expect("AREA.Select failed: {e}").to_equal("")
val print_result = t32_hw_run_cmd(client, "PRINT \"headless_test\"")
match print_result:
    Ok(_): expect("print ok").to_contain("ok")
    Err(e): expect("PRINT failed: {e}").to_equal("")
val view = t32_hw_run_cmd(client, "AREA.view")
match view:
    Ok(_): expect("view ok").to_contain("ok")
    Err(e): expect("AREA.view failed: {e}").to_equal("")
```

</details>

#### PRINT works headless on all versions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# PRINT is available in all T32 versions
val result = t32_hw_run_cmd(client, "PRINT \"headless_universal\"")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("PRINT failed: {e}").to_equal("")
```

</details>

#### eval works in headless

1. Ok
2. Err
   - Expected: "VERSION.BUILD() failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_eval(client, "VERSION.BUILD()")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("VERSION.BUILD() failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/28_setup_headless_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 setup headless

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
