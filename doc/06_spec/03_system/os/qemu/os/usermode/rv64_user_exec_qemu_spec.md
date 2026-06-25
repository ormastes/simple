# Rv64 User Exec Qemu Specification

> <details>

<!-- sdn-diagram:id=rv64_user_exec_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_user_exec_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_user_exec_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_user_exec_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rv64 User Exec Qemu Specification

## Scenarios

### RV64 User-Mode Execution

<details>
<summary>Advanced: trap vector installed</summary>

#### trap vector installed _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("trap vector installed")
```

</details>


</details>

<details>
<summary>Advanced: trap runtime installed</summary>

#### trap runtime installed _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("trap runtime installed")
```

</details>


</details>

<details>
<summary>Advanced: user task spawned from proof binary</summary>

#### user task spawned from proof binary _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("spawned user task")
```

</details>


</details>

<details>
<summary>Advanced: entering U-mode at correct entry point</summary>

#### entering U-mode at correct entry point _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("entering U-mode")
```

</details>


</details>

<details>
<summary>Advanced: user debug_write syscall produces serial output</summary>

#### user debug_write syscall produces serial output _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("P")
    expect(verify_qemu_formal_output(ARCH, output).is_ok()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: boot sequence completes after user task</summary>

#### boot sequence completes after user task _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("boot complete")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/usermode/rv64_user_exec_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RV64 User-Mode Execution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 6 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
