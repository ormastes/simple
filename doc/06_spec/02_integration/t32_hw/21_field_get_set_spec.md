# 21 Field Get Set Specification

> 1. Ok

<!-- sdn-diagram:id=21_field_get_set_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=21_field_get_set_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

21_field_get_set_spec -> std
21_field_get_set_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=21_field_get_set_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 21 Field Get Set Specification

## Scenarios

### T32 field get/set

#### register reads

#### reads PC register via eval

1. Ok
2. Err
   - Expected: "eval PC failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_eval(client, "Register(PC)")
match result:
    Ok(v):
        # PC should return a hex value string
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("eval PC failed: {e}").to_equal("")
```

</details>

#### reads SP register via eval

1. Ok
2. Err
   - Expected: "eval SP failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_eval(client, "Register(SP)")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("eval SP failed: {e}").to_equal("")
```

</details>

#### register writes

#### writes PC register

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_run_cmd(client, "Register.Set PC 0x08000000")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("Register.Set PC failed: {e}").to_equal("")
```

</details>

#### verifies PC was set

1. t32 hw run cmd
2. Ok
3. Err
   - Expected: "verify PC failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Write a known value then read it back
t32_hw_run_cmd(client, "Register.Set PC 0x08000000")
val result = t32_hw_eval(client, "Register(PC)")
match result:
    Ok(v):
        expect(v).to_contain("08000000")
    Err(e):
        expect("verify PC failed: {e}").to_equal("")
```

</details>

#### system mode

#### reads system mode field

1. Ok
2. Err
   - Expected: "SYStem.MODE() failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_eval(client, "SYStem.MODE()")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("SYStem.MODE() failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/21_field_get_set_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 field get/set

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
