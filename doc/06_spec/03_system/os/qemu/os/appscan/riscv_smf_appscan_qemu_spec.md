# Riscv Smf Appscan Qemu Specification

> <details>

<!-- sdn-diagram:id=riscv_smf_appscan_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv_smf_appscan_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv_smf_appscan_qemu_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv_smf_appscan_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv Smf Appscan Qemu Specification

## Scenarios

### RISC-V SMF appscan QEMU

<details>
<summary>Advanced: discovers and launches RV32 SMF apps through the supported filesystem lane</summary>

#### discovers and launches RV32 SMF apps through the supported filesystem lane _(slow)_

1.  assert riscv smf appscan


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run("qemu-system-riscv32"):
    _assert_riscv_smf_appscan(_riscv32_output(), "riscv32")
```

</details>


</details>

<details>
<summary>Advanced: discovers and launches RV64 SMF apps through the supported filesystem lane</summary>

#### discovers and launches RV64 SMF apps through the supported filesystem lane _(slow)_

1.  assert riscv smf appscan


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run("qemu-system-riscv64"):
    _assert_riscv_smf_appscan(_riscv64_output(), "riscv64")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/appscan/riscv_smf_appscan_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RISC-V SMF appscan QEMU

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 2 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
