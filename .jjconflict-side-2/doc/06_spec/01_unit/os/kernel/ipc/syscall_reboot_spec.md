# Syscall Reboot Specification

> _Verifies syscall id 16 behavior that can be checked in hosted tests._

<!-- sdn-diagram:id=syscall_reboot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=syscall_reboot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

syscall_reboot_spec -> std
syscall_reboot_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=syscall_reboot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Syscall Reboot Specification

## Scenarios

### system reboot syscall
_Verifies syscall id 16 behavior that can be checked in hosted tests._

#### routes reboot requests through the platform reset facade

1. hal reset set test mode
   - Expected: result.value equals `0`
   - Expected: hal_reset_requested_for_test() is true
2. hal reset set test mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
hal_reset_set_test_mode(true)
val result = _handle_system_reboot(
    SyscallArgs(
        id: 16,
        arg0: 0,
        arg1: 0,
        arg2: 0,
        arg3: 0,
        arg4: 0,
        arg5: 0
    )
)
expect(result.value).to_equal(0)
expect(hal_reset_requested_for_test()).to_equal(true)
hal_reset_set_test_mode(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/ipc/syscall_reboot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- system reboot syscall

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
