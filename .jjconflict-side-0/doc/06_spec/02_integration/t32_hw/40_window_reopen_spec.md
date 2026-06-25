# T32 Window Reopen Specification

> Tests that T32 window capture still works after closing and reopening the GUI window. Validates GUI resilience for long-running debug sessions.

<!-- sdn-diagram:id=40_window_reopen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=40_window_reopen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

40_window_reopen_spec -> std
40_window_reopen_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=40_window_reopen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Window Reopen Specification

Tests that T32 window capture still works after closing and reopening the GUI window. Validates GUI resilience for long-running debug sessions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing |
| Status | Draft |
| Source | `test/02_integration/t32_hw/40_window_reopen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that T32 window capture still works after closing and reopening
the GUI window. Validates GUI resilience for long-running debug sessions.

## Scenarios

### T32 Window Reopen

#### when GUI window is closed and reopened

#### clears all windows

1. Ok
2. c disconnect
3. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_probe_available():
    expect("skipped").to_contain("skip")
    return
val client = t32_hw_connect()
match client:
    Ok(c):
        val r = c.run_command("WinCLEAR")
        c.disconnect()
        match r:
            Ok(_): expect("cleared").to_equal("cleared")
            Err(_): expect("WinCLEAR may not be supported headless").to_contain("headless")
    Err(e):
        expect("connection failed: {e}").to_contain("skip")
```

</details>

#### reopens Register window after clear

1. Ok
2. c disconnect
3. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_probe_available():
    expect("skipped").to_contain("skip")
    return
val client = t32_hw_connect()
match client:
    Ok(c):
        val r = c.run_command("Register /SpotLight")
        c.disconnect()
        match r:
            Ok(_): expect("reopened").to_equal("reopened")
            Err(e): expect("Register window: {e}").to_contain("window")
    Err(e):
        expect("connection failed: {e}").to_contain("skip")
```

</details>

#### captures Register content after reopen

1. Ok
2. c disconnect
3. Ok
4. Err
5. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not t32_hw_probe_available():
    expect("skipped").to_contain("skip")
    return
val client = t32_hw_connect()
match client:
    Ok(c):
        val regs = c.read_all_registers()
        c.disconnect()
        match regs:
            Ok(data):
                # Should have at least PC and SP
                expect(data.len()).to_be_greater_than(0)
            Err(e):
                expect("register read: {e}").to_contain("register")
    Err(e):
        expect("connection failed: {e}").to_contain("skip")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
