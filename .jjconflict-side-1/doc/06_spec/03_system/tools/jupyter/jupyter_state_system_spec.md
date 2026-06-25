# Jupyter State System Specification

> <details>

<!-- sdn-diagram:id=jupyter_state_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=jupyter_state_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

jupyter_state_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=jupyter_state_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jupyter State System Specification

## Scenarios

### Jupyter Kernel State

<details>
<summary>Advanced: should execute code and produce output</summary>

#### should execute code and produce output _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msgs = "{\"channel\":\"shell\",\"msg_type\":\"execute_request\",\"msg_id\":\"e1\",\"session\":\"s1\",\"content\":{\"code\":\"print 42\"}}\n{\"channel\":\"control\",\"msg_type\":\"shutdown_request\",\"msg_id\":\"s1\",\"session\":\"s1\",\"content\":{}}\n"
val output = send_kernel_messages(msgs)
expect(output).to_contain("execute_reply")
```

</details>


</details>

<details>
<summary>Advanced: should handle execute errors gracefully</summary>

#### should handle execute errors gracefully _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msgs = "{\"channel\":\"shell\",\"msg_type\":\"execute_request\",\"msg_id\":\"e2\",\"session\":\"s1\",\"content\":{\"code\":\"this is invalid\"}}\n{\"channel\":\"control\",\"msg_type\":\"shutdown_request\",\"msg_id\":\"s2\",\"session\":\"s1\",\"content\":{}}\n"
val output = send_kernel_messages(msgs)
expect(output).to_contain("execute_reply")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/jupyter/jupyter_state_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Jupyter Kernel State

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 2 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
