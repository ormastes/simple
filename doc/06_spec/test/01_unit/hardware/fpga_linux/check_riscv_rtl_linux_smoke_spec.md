# Check Riscv Rtl Linux Smoke Specification

> <details>

<!-- sdn-diagram:id=check_riscv_rtl_linux_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=check_riscv_rtl_linux_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

check_riscv_rtl_linux_smoke_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=check_riscv_rtl_linux_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Check Riscv Rtl Linux Smoke Specification

## Scenarios

### RISC-V RTL Linux smoke gate script

#### keeps RV32 and RV64 as symmetric public lane selectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = rt_file_read_text("scripts/check/check-riscv-rtl-linux-smoke.shs")
expect(script).to_contain("--rv32-only")
expect(script).to_contain("--rv64-only")
expect(script).to_contain("run_lane \"generated_rv32_linux\"")
expect(script).to_contain("run_lane \"generated_rv64_linux\"")
expect(script.contains("--generated-rv64-only")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/hardware/fpga_linux/check_riscv_rtl_linux_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RISC-V RTL Linux smoke gate script

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
