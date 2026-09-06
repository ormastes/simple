# Riscv Generated Core Specification

> Tests covering RISC-V generated core proof lanes, RISC-V generated core shell contracts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv Generated Core Specification

## Scenarios

### RISC-V generated core proof lanes

#### keeps generated RV32 and RV64 Linux lanes public and Linux-capable

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps generated RV32 and RV64 Linux lanes public and Linux-capable
   - Expected: RiscvProofLane.GeneratedRv32Linux.to_text() equals `generated_rv32_linux`
   - Expected: RiscvProofLane.GeneratedRv64Linux.to_text() equals `generated_rv64_linux`
   - Expected: RiscvProofLane.GeneratedRv32Linux.requires_linux_boot() is true
   - Expected: RiscvProofLane.GeneratedRv64Linux.is_external_reference() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps generated RV32 and RV64 Linux lanes public and Linux-capable")
expect(RiscvProofLane.GeneratedRv32Linux.to_text()).to_equal("generated_rv32_linux")
expect(RiscvProofLane.GeneratedRv64Linux.to_text()).to_equal("generated_rv64_linux")
expect(RiscvProofLane.GeneratedRv32Linux.requires_linux_boot()).to_equal(true)
expect(RiscvProofLane.GeneratedRv64Linux.is_external_reference()).to_equal(false)
```

</details>

### RISC-V generated core shell contracts

#### defines RV32 on the Linux fw_jump/OpenSBI proof path

- defines RV32 on the Linux fw_jump/OpenSBI proof path
   - Expected: shell.xlen_bits equals `32`
   - Expected: shell.proof_lane equals `RiscvProofLane.GeneratedRv32Linux`
   - Expected: shell.boot.opensbi_fw_jump is true
   - Expected: shell.boot.hartid_register equals `a0`
   - Expected: shell.boot.dtb_register equals `a1`
   - Expected: shell.shell_services_summary() equals `none`
   - Expected: metadata.schema_version equals `riscv_rtl_debuggability_lint/v1`
   - Expected: metadata.lane_id equals `rv32`
   - Expected: metadata.runner_testbenches.len() equals `2`
   - Expected: metadata.runner_testbenches[0].file_name equals `tb_generated_rv32_linux_handoff.vhd`
   - Expected: metadata.runner_testbenches[0].pass_marker equals `GENERATED_RV32_LINUX_HANDOFF: PASS`
   - Expected: metadata.runner_testbenches[1].file_name equals `tb_generated_rv32_boot_info_real_dtb.vhd`
   - Expected: metadata.runner_testbenches[1].pass_marker equals `GENERATED_RV32_BOOT_INFO_REAL_DTB: PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines RV32 on the Linux fw_jump/OpenSBI proof path")
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

- defines RV64 on the Linux fw_jump/OpenSBI proof path
   - Expected: shell.xlen_bits equals `64`
   - Expected: shell.proof_lane equals `RiscvProofLane.GeneratedRv64Linux`
   - Expected: shell.boot.opensbi_fw_jump is true
   - Expected: shell.boot.hartid_register equals `a0`
   - Expected: shell.boot.dtb_register equals `a1`
   - Expected: metadata.lane_id equals `rv64`
   - Expected: metadata.runner_testbenches.len() equals `7`
   - Expected: metadata.runner_testbenches[0].file_name equals `tb_generated_rv64_linux_handoff.vhd`
   - Expected: metadata.runner_testbenches[0].pass_marker equals `GENERATED_RV64_LINUX_HANDOFF: PASS`
   - Expected: metadata.runner_testbenches[2].file_name equals `tb_generated_rv64_boot_info_dtb.vhd`
   - Expected: metadata.runner_testbenches[2].pass_marker equals `GENERATED_RV64_BOOT_INFO_DTB: PASS`
   - Expected: metadata.runner_testbenches[6].file_name equals `tb_generated_rv64_sv39_fault.vhd`
   - Expected: metadata.runner_testbenches[6].pass_marker equals `GENERATED_RV64_SV39_FAULT: PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines RV64 on the Linux fw_jump/OpenSBI proof path")
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
| Source | `test/unit/hardware/riscv_common/riscv_generated_core_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RISC-V generated core proof lanes, RISC-V generated core shell contracts.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3f7e071d6c5e69f0c7776738fc181c4916f5d5b11c77921ba1dd0cffa8aaa59f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3f7e071d6c5e69f0c7776738fc181c4916f5d5b11c77921ba1dd0cffa8aaa59f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3f7e071d6c5e69f0c7776738fc181c4916f5d5b11c77921ba1dd0cffa8aaa59f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/hardware/riscv_common/riscv_generated_core_spec.spl
mirror: doc/06_spec/unit/hardware/riscv_common/riscv_generated_core_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/hardware/riscv_common/riscv_generated_core_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/hardware/riscv_common/riscv_generated_core_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/hardware/riscv_common/riscv_generated_core_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/hardware/riscv_common/riscv_generated_core_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps generated RV32 and RV64 Linux lanes public and Linux-capable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/riscv_common/riscv_generated_core_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines RV32 on the Linux fw_jump/OpenSBI proof path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/riscv_common/riscv_generated_core_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines RV64 on the Linux fw_jump/OpenSBI proof path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
