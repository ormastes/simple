# Riscv Generated Core Specification

> <details>

<!-- sdn-diagram:id=riscv_generated_core_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv_generated_core_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv_generated_core_spec -> std
riscv_generated_core_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv_generated_core_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv Generated Core Specification

## Scenarios

### RISC-V generated core proof lanes

#### keeps generated RV32 and RV64 Linux lanes public and Linux-capable

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(RiscvProofLane.GeneratedRv32Linux.to_text()).to_equal("generated_rv32_linux")
expect(RiscvProofLane.GeneratedRv64Linux.to_text()).to_equal("generated_rv64_linux")
expect(RiscvProofLane.GeneratedRv32Linux.requires_linux_boot()).to_equal(true)
expect(RiscvProofLane.GeneratedRv64Linux.is_external_reference()).to_equal(false)
```

</details>

### RISC-V generated core shell contracts

#### defines RV32 on the Linux fw_jump/OpenSBI proof path

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shell = GeneratedCoreShellContract.rv32_linux()
val metadata = shell.debug_metadata()
expect(shell.xlen_bits).to_equal(32)
expect(shell.proof_lane).to_equal(RiscvProofLane.GeneratedRv32Linux)
expect(shell.boot.opensbi_fw_jump).to_equal(true)
expect(shell.boot.hartid_register).to_equal("a0")
expect(shell.boot.dtb_register).to_equal("a1")
expect(shell.acceptance_markers()).to_contain("Linux version")
expect(shell.shell_services_summary()).to_equal("none")
expect(metadata.schema_version).to_equal("riscv_rtl_debuggability_lint/v1")
expect(metadata.lane_id).to_equal("rv32")
expect(metadata.debug_outputs).to_contain("semi_trigger")
expect(metadata.source_map.len()).to_be_greater_than(10)
expect(metadata.report_markers).to_contain("DTB_PROBE_SEEN:")
expect(metadata.report_markers).to_contain("FINAL_PC_HEX32:")
expect(metadata.runner_testbenches.len()).to_equal(2)
expect(metadata.runner_testbenches[0].file_name).to_equal("tb_generated_rv32_linux_handoff.vhd")
expect(metadata.runner_testbenches[0].pass_marker).to_equal("GENERATED_RV32_LINUX_HANDOFF: PASS")
expect(metadata.runner_testbenches[1].file_name).to_equal("tb_generated_rv32_boot_info_real_dtb.vhd")
expect(metadata.runner_testbenches[1].pass_marker).to_equal("GENERATED_RV32_BOOT_INFO_REAL_DTB: PASS")
```

</details>

#### defines RV64 on the Linux fw_jump/OpenSBI proof path

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shell = GeneratedCoreShellContract.rv64_linux()
val metadata = shell.debug_metadata()
expect(shell.xlen_bits).to_equal(64)
expect(shell.proof_lane).to_equal(RiscvProofLane.GeneratedRv64Linux)
expect(shell.boot.opensbi_fw_jump).to_equal(true)
expect(shell.boot.hartid_register).to_equal("a0")
expect(shell.boot.dtb_register).to_equal("a1")
expect(shell.acceptance_markers()).to_contain("Linux version")
expect(shell.interrupt_inputs).to_contain("supervisor_external")
expect(shell.debug_outputs).to_contain("semi_trigger")
expect(metadata.lane_id).to_equal("rv64")
expect(metadata.debug_outputs).to_contain("debug_pc")
expect(metadata.report_markers).to_contain("TRAP_EDGE_PC_HEX32")
expect(metadata.report_markers).to_contain("PC_LOW32:")
expect(metadata.report_markers).to_contain("TRAP_CAUSE_WORD:")
expect(metadata.runner_testbenches.len()).to_equal(7)
expect(metadata.runner_testbenches[0].file_name).to_equal("tb_generated_rv64_linux_handoff.vhd")
expect(metadata.runner_testbenches[0].pass_marker).to_equal("GENERATED_RV64_LINUX_HANDOFF: PASS")
expect(metadata.runner_testbenches[2].file_name).to_equal("tb_generated_rv64_boot_info_dtb.vhd")
expect(metadata.runner_testbenches[2].pass_marker).to_equal("GENERATED_RV64_BOOT_INFO_DTB: PASS")
expect(metadata.runner_testbenches[6].file_name).to_equal("tb_generated_rv64_sv39_fault.vhd")
expect(metadata.runner_testbenches[6].pass_marker).to_equal("GENERATED_RV64_SV39_FAULT: PASS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/hardware/riscv_common/riscv_generated_core_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RISC-V generated core proof lanes
- RISC-V generated core shell contracts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
