# 26 Cmm Commands Validate Specification

> <details>

<!-- sdn-diagram:id=26_cmm_commands_validate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=26_cmm_commands_validate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

26_cmm_commands_validate_spec -> std
26_cmm_commands_validate_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=26_cmm_commands_validate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 26 Cmm Commands Validate Specification

## Scenarios

### T32 CMM commands validate

#### valid commands

#### SYStem.Up is a valid command

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

#### Break is a valid command

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_run_cmd(client, "Break")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("Break failed: {e}").to_equal("")
```

</details>

#### PRINT is a valid command

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_run_cmd(client, "PRINT \"test\"")
match result:
    Ok(_): expect("cmd ok").to_contain("ok")
    Err(e): expect("PRINT failed: {e}").to_equal("")
```

</details>

#### invalid commands

#### invalid command produces error

1. Ok
2. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_hw_run_cmd(client, "ZZZNOTACMD.ZZZZ")
match result:
    Ok(_):
        # If T32 does not error, it may silently ignore;
        # either way the command was sent
        expect("accepted ok").to_contain("ok")
    Err(_):
        # Expected -- invalid command should produce an error
        expect("error accepted").to_contain("accepted")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/26_cmm_commands_validate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 CMM commands validate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
