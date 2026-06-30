# Jupyter Execution System Specification

> <details>

<!-- sdn-diagram:id=jupyter_execution_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=jupyter_execution_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

jupyter_execution_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=jupyter_execution_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jupyter Execution System Specification

## Scenarios

### Jupyter Kernel Execution

<details>
<summary>Advanced: should respond to kernel_info_request</summary>

#### should respond to kernel_info_request _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "{\"channel\":\"shell\",\"msg_type\":\"kernel_info_request\",\"msg_id\":\"test1\",\"session\":\"s1\",\"content\":{}}"
val output = send_kernel_message(msg)
expect(output).to_contain("kernel_info_reply")
expect(output).to_contain("simple")
```

</details>


</details>

<details>
<summary>Advanced: should respond to shutdown_request</summary>

#### should respond to shutdown_request _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "{\"channel\":\"control\",\"msg_type\":\"shutdown_request\",\"msg_id\":\"test2\",\"session\":\"s1\",\"content\":{}}"
val output = send_kernel_message(msg)
expect(output).to_contain("shutdown_reply")
```

</details>


</details>

<details>
<summary>Advanced: should handle is_complete_request for complete code</summary>

#### should handle is_complete_request for complete code _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "{\"channel\":\"shell\",\"msg_type\":\"is_complete_request\",\"msg_id\":\"test3\",\"session\":\"s1\",\"content\":{\"code\":\"val x = 42\"}}"
val output = send_kernel_message(msg)
expect(output).to_contain("complete")
```

</details>


</details>

<details>
<summary>Advanced: should handle is_complete_request for incomplete code</summary>

#### should handle is_complete_request for incomplete code _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "{\"channel\":\"shell\",\"msg_type\":\"is_complete_request\",\"msg_id\":\"test4\",\"session\":\"s1\",\"content\":{\"code\":\"fn foo():\"}}"
val output = send_kernel_message(msg)
expect(output).to_contain("incomplete")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/jupyter/jupyter_execution_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Jupyter Kernel Execution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
