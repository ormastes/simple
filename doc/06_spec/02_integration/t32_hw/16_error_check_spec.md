# 16 Error Check Specification

> <details>

<!-- sdn-diagram:id=16_error_check_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=16_error_check_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

16_error_check_spec -> std
16_error_check_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=16_error_check_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 16 Error Check Specification

## Scenarios

### T32 error check

#### error state queries

#### error check after clean state

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_eval(client, "MESSAGE.STRing()")
match result:
    Ok(_): expect("eval ok").to_contain("ok")
    Err(e): expect("MESSAGE.STRing failed: {e}").to_equal("")
```

</details>

#### forces error via bad cmd

1. Ok
2. Err
   - Expected: "MESSAGE.STRing after bad cmd failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Run invalid command to produce an error
val _ = t32_hw_run_cmd(client, "NONEXISTENT.COMMAND.12345")
# Then query the error message
val result = t32_hw_eval(client, "MESSAGE.STRing()")
match result:
    Ok(v):
        # After a bad command, message string should be non-empty
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("MESSAGE.STRing after bad cmd failed: {e}").to_equal("")
```

</details>

#### error state is queryable

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_eval(client, "MESSAGE.NUMber()")
match result:
    Ok(_): expect("eval ok").to_contain("ok")
    Err(e): expect("MESSAGE.NUMber failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/16_error_check_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 error check

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
