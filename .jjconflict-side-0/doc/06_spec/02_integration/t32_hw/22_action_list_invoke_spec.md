# 22 Action List Invoke Specification

> <details>

<!-- sdn-diagram:id=22_action_list_invoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=22_action_list_invoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

22_action_list_invoke_spec -> std
22_action_list_invoke_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=22_action_list_invoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 22 Action List Invoke Specification

## Scenarios

### T32 action list invoke

#### execution control

#### Go starts target

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val go_result = t32_hw_run_cmd(client, "Go")
match go_result:
    Ok(_): expect("go ok").to_contain("ok")
    Err(e): expect("Go failed: {e}").to_equal("")
val state = t32_hw_eval(client, "STATE.RUN()")
match state:
    Ok(v): expect(v).to_contain("TRUE")
    Err(e): expect("STATE.RUN() failed: {e}").to_equal("")
```

</details>

#### Break stops target

1. t32 hw run cmd


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
t32_hw_run_cmd(client, "Go")
val brk_result = t32_hw_run_cmd(client, "Break")
match brk_result:
    Ok(_): expect("break ok").to_contain("ok")
    Err(e): expect("Break failed: {e}").to_equal("")
val state = t32_hw_eval(client, "STATE.RUN()")
match state:
    Ok(v): expect(v).to_contain("FALSE")
    Err(e): expect("STATE.RUN() failed: {e}").to_equal("")
```

</details>

#### Step executes one instruction

1. t32 hw run cmd
2. Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Ensure target is stopped first
t32_hw_run_cmd(client, "Break")
val result = t32_hw_run_cmd(client, "Step")
match result:
    Ok(_):
        val state = t32_hw_eval(client, "STATE.RUN()")
        match state:
            Ok(v): expect(v).to_contain("FALSE")
            Err(e): expect("STATE.RUN() after Step failed: {e}").to_equal("")
    Err(e): expect("Step failed: {e}").to_equal("")
```

</details>

#### Step.Over executes

1. t32 hw run cmd
2. Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
t32_hw_run_cmd(client, "Break")
val result = t32_hw_run_cmd(client, "Step.Over")
match result:
    Ok(_):
        val state = t32_hw_eval(client, "STATE.RUN()")
        match state:
            Ok(v): expect(v).to_contain("FALSE")
            Err(e): expect("STATE.RUN() after Step.Over failed: {e}").to_equal("")
    Err(e): expect("Step.Over failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/22_action_list_invoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 action list invoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
