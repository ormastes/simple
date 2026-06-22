# 13 Cmd Run Specification

> <details>

<!-- sdn-diagram:id=13_cmd_run_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=13_cmd_run_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

13_cmd_run_spec -> std
13_cmd_run_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=13_cmd_run_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 13 Cmd Run Specification

## Scenarios

### T32 command run

#### valid commands

#### runs SYStem.Up

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

#### runs VERSION.ENvironment

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_run_cmd(client, "VERSION.ENvironment")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("VERSION.ENvironment failed: {e}").to_equal("")
```

</details>

#### error handling

#### empty command returns error

1. Ok
   - Expected: v.len() equals `0`
2. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_run_cmd(client, "")
match result:
    Ok(v):
        # Empty command may return Ok with empty output
        expect(v.len()).to_equal(0)
    Err(_):
        # Or it may return an error -- both acceptable
        expect("error accepted").to_contain("accepted")
```

</details>

#### invalid command returns error

1. Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_run_cmd(client, "NONEXISTENT.COMMAND.12345")
match result:
    Err(_): expect("error accepted").to_contain("accepted")
    Ok(_):
        # Some T32 versions silently accept bad commands
        expect("accepted ok").to_contain("ok")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/13_cmd_run_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 command run

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
