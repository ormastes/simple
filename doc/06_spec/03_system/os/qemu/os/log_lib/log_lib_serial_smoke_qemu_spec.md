# Log Lib Serial Smoke Qemu Specification

> <details>

<!-- sdn-diagram:id=log_lib_serial_smoke_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=log_lib_serial_smoke_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

log_lib_serial_smoke_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=log_lib_serial_smoke_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Log Lib Serial Smoke Qemu Specification

## Scenarios

### x86_64 log-lib serial smoke (post-migration)

<details>
<summary>Advanced: boots and emits SimpleOS banner via log lib</summary>

#### boots and emits SimpleOS banner via log lib _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = run_qemu_for_arch(Architecture.X86_64)
    expect(output).to_contain("SimpleOS")
```

</details>


</details>

<details>
<summary>Advanced: emits at least one [INFO]-prefixed line (log_info routed)</summary>

#### emits at least one [INFO]-prefixed line (log_info routed) _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = run_qemu_for_arch(Architecture.X86_64)
    expect(output).to_contain("[INFO]")
```

</details>


</details>

<details>
<summary>Advanced: emits bare [BOOT] marker (log_raw_println preserves wire bytes)</summary>

#### emits bare [BOOT] marker (log_raw_println preserves wire bytes) _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = run_qemu_for_arch(Architecture.X86_64)
    # The forbidden double-prefix shape ('[INFO] [BOOT]') is checked
    # in test/unit/os/kernel/logging/marker_wire_format_spec.spl as a unit
    # test. Here we just confirm the marker reaches serial.
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

<details>
<summary>Advanced: config-driven serial: banner reaches COM1</summary>

#### config-driven serial: banner reaches COM1 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run(Architecture.X86_64):
    val output = run_qemu_for_arch(Architecture.X86_64)
    # If log_set_device_from_profile never wired COM1, or if the
    # runtime hook returned false, no output reaches the serial
    # stream (interpreter fallback doesn't run under QEMU).
    expect(output).to_contain("SimpleOS")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/log_lib/log_lib_serial_smoke_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- x86_64 log-lib serial smoke (post-migration)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
