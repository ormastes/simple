# 19 Resources Specification

> 1. Ok

<!-- sdn-diagram:id=19_resources_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=19_resources_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

19_resources_spec -> std
19_resources_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=19_resources_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 19 Resources Specification

## Scenarios

### T32 resources

#### T32 version resources

#### eval T32 environment

1. Ok
2. Err
   - Expected: "VERSION.ENvironment failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_has_version_env():
    expect("VERSION.ENvironment not available in this T32 version").to_contain("not available")
    return
val result = t32_hw_eval(client, "VERSION.ENvironment()")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("VERSION.ENvironment failed: {e}").to_equal("")
```

</details>

#### eval T32 build date

1. Ok
2. Err
   - Expected: "VERSION.DATE failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_eval(client, "VERSION.DATE()")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("VERSION.DATE failed: {e}").to_equal("")
```

</details>

#### eval T32 software version

1. Ok
2. Err
   - Expected: "VERSION.SOFTWARE failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_eval(client, "VERSION.SOFTWARE()")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("VERSION.SOFTWARE failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/19_resources_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 resources

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
