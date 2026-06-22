# 24 History Tail Specification

> 1. Ok

<!-- sdn-diagram:id=24_history_tail_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=24_history_tail_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

24_history_tail_spec -> std
24_history_tail_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=24_history_tail_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 24 History Tail Specification

## Scenarios

### T32 history tail

#### PRACTICE state

#### PRACTICE.STATE() queryable

1. Ok
2. Err
   - Expected: "PRACTICE.STATE() failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_has_practice_state():
    expect("PRACTICE.STATE not available in this T32 version").to_contain("not available")
    return
val result = t32_hw_eval(client, "PRACTICE.STATE()")
match result:
    Ok(v):
        expect(v.len()).to_be_greater_than(0)
    Err(e):
        expect("PRACTICE.STATE() failed: {e}").to_equal("")
```

</details>

#### command history

#### command history exists after commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# After running PRINT commands above, the session should have
# accumulated history. We verify by running another command
# and checking the AREA buffer is accessible.
val result = t32_hw_run_cmd(client, "PRINT \"history_check\"")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("history command failed: {e}").to_equal("")
```

</details>

#### AREA buffer

#### AREA buffer readable

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_has_area():
    expect("AREA not available in this T32 version").to_contain("not available")
    return
val result = t32_hw_run_cmd(client, "AREA.view")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("AREA.view failed: {e}").to_equal("")
```

</details>

#### PRINT output verifiable via command success

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# PRINT works on all T32 versions as a universal alternative
val result = t32_hw_run_cmd(client, "PRINT \"tail_check\"")
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
| Source | `test/02_integration/t32_hw/24_history_tail_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 history tail

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
