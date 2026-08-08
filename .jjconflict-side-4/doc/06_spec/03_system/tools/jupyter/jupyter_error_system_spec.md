# Jupyter Error System Specification

> <details>

<!-- sdn-diagram:id=jupyter_error_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=jupyter_error_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

jupyter_error_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=jupyter_error_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jupyter Error System Specification

## Scenarios

### Jupyter Kernel Error Handling

<details>
<summary>Advanced: should report errors for bad code</summary>

#### should report errors for bad code _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msgs = "{\"channel\":\"shell\",\"msg_type\":\"execute_request\",\"msg_id\":\"err1\",\"session\":\"s1\",\"content\":{\"code\":\"val = \"}}\n{\"channel\":\"control\",\"msg_type\":\"shutdown_request\",\"msg_id\":\"s2\",\"session\":\"s1\",\"content\":{}}\n"
val output = send_kernel_messages(msgs)
# Should get error reply, not crash
expect(output).to_contain("execute_reply")
```

</details>


</details>

<details>
<summary>Advanced: should survive error and handle next request</summary>

#### should survive error and handle next request _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msgs = "{\"channel\":\"shell\",\"msg_type\":\"execute_request\",\"msg_id\":\"err2\",\"session\":\"s1\",\"content\":{\"code\":\"bad code\"}}\n{\"channel\":\"shell\",\"msg_type\":\"execute_request\",\"msg_id\":\"ok1\",\"session\":\"s1\",\"content\":{\"code\":\"print 42\"}}\n{\"channel\":\"control\",\"msg_type\":\"shutdown_request\",\"msg_id\":\"s3\",\"session\":\"s1\",\"content\":{}}\n"
val output = send_kernel_messages(msgs)
expect(output).to_contain("execute_reply")
```

</details>


</details>

<details>
<summary>Advanced: should handle comm_info_request</summary>

#### should handle comm_info_request _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msgs = "{\"channel\":\"shell\",\"msg_type\":\"comm_info_request\",\"msg_id\":\"ci1\",\"session\":\"s1\",\"content\":{}}\n{\"channel\":\"control\",\"msg_type\":\"shutdown_request\",\"msg_id\":\"s4\",\"session\":\"s1\",\"content\":{}}\n"
val output = send_kernel_messages(msgs)
expect(output).to_contain("comm_info_reply")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/jupyter/jupyter_error_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Jupyter Kernel Error Handling

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
