# Simpleos Board Hardening Specification

> Tests covering SimpleOS board hardening catalog.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Board Hardening Specification

## Scenarios

### SimpleOS board hardening catalog

#### defines optional protection modes and real board/QEMU contracts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines optional protection modes and real board/QEMU contracts
   - Expected: simpleos_protection_mode_from_text("off") equals `SimpleOsProtectionMode.Off`
   - Expected: simpleos_protection_mode_from_text("detect") equals `SimpleOsProtectionMode.Detect`
   - Expected: simpleos_protection_mode_from_text("enforce") equals `SimpleOsProtectionMode.Enforce`
   - Expected: simpleos_protection_mode_from_text("fault-test") equals `SimpleOsProtectionMode.FaultTest`
   - Expected: simpleos_protection_mode_name(SimpleOsProtectionMode.FaultTest) equals `fault-test`
   - Expected: simpleos_protection_mode_accepts_hardening(SimpleOsProtectionMode.Off) is false
   - Expected: simpleos_protection_mode_accepts_hardening(SimpleOsProtectionMode.Detect) is false
   - Expected: simpleos_protection_mode_accepts_hardening(SimpleOsProtectionMode.Enforce) is true
   - Expected: simpleos_protection_mode_accepts_hardening(SimpleOsProtectionMode.FaultTest) is true
   - Expected: simpleos_board_known("mps2-an505") is true
   - Expected: simpleos_board_cpu("mps2-an505") equals `cortex-m33`
   - Expected: simpleos_board_has_qemu_id("mps2-an505") is true
   - Expected: cmd.len() equals `14`
   - Expected: cmd[0] equals `qemu-system-arm`
   - Expected: cmd[1] equals `-machine`
   - Expected: cmd[2] equals `mps2-an505`
   - Expected: cmd[3] equals `-cpu`
   - Expected: cmd[4] equals `cortex-m33`
   - Expected: cmd[5] equals `-kernel`
   - Expected: cmd[6] equals `build/os/simpleos_cm33.elf`
   - Expected: cmd[7] equals `-serial`
   - Expected: cmd[8] equals `stdio`
   - Expected: cmd[9] equals `-monitor`
   - Expected: cmd[10] equals `none`
   - Expected: cmd[11] equals `-display`
   - Expected: cmd[12] equals `none`
   - Expected: cmd[13] equals `-no-reboot`
   - Expected: smoke_cmd[0] equals `env`
   - Expected: smoke_cmd[1] equals `SIMPLEOS_PROTECTION_MODE=fault-test`
   - Expected: smoke_cmd[2] equals `qemu-system-arm`
   - Expected: simpleos_board_qemu_requires_semihosting_for_mode("mps2-an505", SimpleOsProtectionMode.FaultTest) is true
   - Expected: simpleos_board_qemu_requires_semihosting_for_mode("mps2-an505", SimpleOsProtectionMode.Enforce) is false
   - Expected: rv_cmd[0] equals `env`
   - Expected: rv_cmd[1] equals `SIMPLEOS_PROTECTION_MODE=enforce`
   - Expected: rv_cmd[2] equals `qemu-system-riscv64`
   - Expected: simpleos_board_has_qemu_id("ra4m1-uno-r4") is false
   - Expected: simpleos_board_has_qemu_id("stm32u585-uno-q") is false
   - Expected: simpleos_board_physical_script("ra4m1-uno-r4") equals `scripts/run_simpleos_ra4m1.shs`
   - Expected: simpleos_board_physical_script("stm32u585-uno-q") equals `scripts/run_simpleos_stm32u585.shs`
   - Expected: simpleos_board_known("up-squared-apollo-lake") is true
   - Expected: simpleos_board_cpu("up-squared-apollo-lake") equals `x86_64-apollo-lake`
   - Expected: simpleos_board_has_qemu_id("up-squared-apollo-lake") is false
   - Expected: simpleos_board_physical_script("up-squared-apollo-lake") equals `scripts/os/run_simpleos_up_squared_apl.shs`
   - Expected: up2_cmd equals `["sh", "scripts/os/run_simpleos_up_squared_apl.shs", "--build-only", "--prote... (full value in folded executable source)`
   - Expected: ra_cmd equals `["sh", "scripts/run_simpleos_ra4m1.shs", "--build-only", "--protection=fault-... (full value in folded executable source)`
   - Expected: u585_cmd equals `["sh", "scripts/run_simpleos_stm32u585.shs", "--build-only", "--protection=en... (full value in folded executable source)`
   - Expected: serial_cmd equals `[`
   - Expected: simpleos_board_qemu_command_for_id("ra4m1-uno-r4", "ignored").len() equals `0`
   - Expected: simpleos_board_supports_protection_mode_id("stm32u585-uno-q", SimpleOsProtectionMode.Off) is true
   - Expected: simpleos_board_supports_protection_mode_id("stm32u585-uno-q", SimpleOsProtectionMode.Detect) is true
   - Expected: simpleos_board_supports_protection_mode_id("stm32u585-uno-q", SimpleOsProtectionMode.Enforce) is true
   - Expected: simpleos_board_supports_protection_mode_id("stm32u585-uno-q", SimpleOsProtectionMode.FaultTest) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 98 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines optional protection modes and real board/QEMU contracts")
expect(simpleos_protection_mode_from_text("off")).to_equal(SimpleOsProtectionMode.Off)
expect(simpleos_protection_mode_from_text("detect")).to_equal(SimpleOsProtectionMode.Detect)
expect(simpleos_protection_mode_from_text("enforce")).to_equal(SimpleOsProtectionMode.Enforce)
expect(simpleos_protection_mode_from_text("fault-test")).to_equal(SimpleOsProtectionMode.FaultTest)
expect(simpleos_protection_mode_from_text("fallback")).to_be_nil()
expect(simpleos_protection_mode_name(SimpleOsProtectionMode.FaultTest)).to_equal("fault-test")

expect(simpleos_protection_mode_accepts_hardening(SimpleOsProtectionMode.Off)).to_equal(false)
expect(simpleos_protection_mode_accepts_hardening(SimpleOsProtectionMode.Detect)).to_equal(false)
expect(simpleos_protection_mode_accepts_hardening(SimpleOsProtectionMode.Enforce)).to_equal(true)
expect(simpleos_protection_mode_accepts_hardening(SimpleOsProtectionMode.FaultTest)).to_equal(true)

expect(simpleos_board_known("mps2-an505")).to_equal(true)
expect(simpleos_board_cpu("mps2-an505")).to_equal("cortex-m33")
expect(simpleos_board_has_qemu_id("mps2-an505")).to_equal(true)
expect(simpleos_board_protection_marker_for_id("mps2-an505", SimpleOsProtectionMode.Enforce)).to_contain("kind=pmsav8-mpu")

val cmd = simpleos_board_qemu_command_for_id("mps2-an505", "build/os/simpleos_cm33.elf")
expect(cmd.len()).to_equal(14)
expect(cmd[0]).to_equal("qemu-system-arm")
expect(cmd[1]).to_equal("-machine")
expect(cmd[2]).to_equal("mps2-an505")
expect(cmd[3]).to_equal("-cpu")
expect(cmd[4]).to_equal("cortex-m33")
expect(cmd[5]).to_equal("-kernel")
expect(cmd[6]).to_equal("build/os/simpleos_cm33.elf")
expect(cmd[7]).to_equal("-serial")
expect(cmd[8]).to_equal("stdio")
expect(cmd[9]).to_equal("-monitor")
expect(cmd[10]).to_equal("none")
expect(cmd[11]).to_equal("-display")
expect(cmd[12]).to_equal("none")
expect(cmd[13]).to_equal("-no-reboot")

val smoke_cmd = simpleos_board_qemu_command_for_id_with_mode(
    "mps2-an505",
    "build/os/simpleos_cm33.elf",
    SimpleOsProtectionMode.FaultTest
)
expect(smoke_cmd[0]).to_equal("env")
expect(smoke_cmd[1]).to_equal("SIMPLEOS_PROTECTION_MODE=fault-test")
expect(smoke_cmd[2]).to_equal("qemu-system-arm")
expect(smoke_cmd).to_contain("-semihosting-config")
expect(smoke_cmd).to_contain("enable=on,target=native")
expect(simpleos_board_qemu_requires_semihosting_for_mode("mps2-an505", SimpleOsProtectionMode.FaultTest)).to_equal(true)
expect(simpleos_board_qemu_requires_semihosting_for_mode("mps2-an505", SimpleOsProtectionMode.Enforce)).to_equal(false)

val rv_cmd = simpleos_board_qemu_command_for_id_with_mode(
    "riscv64-virt",
    "build/os/simpleos_rv64.elf",
    SimpleOsProtectionMode.Enforce
)
expect(rv_cmd[0]).to_equal("env")
expect(rv_cmd[1]).to_equal("SIMPLEOS_PROTECTION_MODE=enforce")
expect(rv_cmd[2]).to_equal("qemu-system-riscv64")

expect(simpleos_board_has_qemu_id("ra4m1-uno-r4")).to_equal(false)
expect(simpleos_board_has_qemu_id("stm32u585-uno-q")).to_equal(false)
expect(simpleos_board_physical_script("ra4m1-uno-r4")).to_equal("scripts/run_simpleos_ra4m1.shs")
expect(simpleos_board_physical_script("stm32u585-uno-q")).to_equal("scripts/run_simpleos_stm32u585.shs")
expect(simpleos_board_known("up-squared-apollo-lake")).to_equal(true)
expect(simpleos_board_cpu("up-squared-apollo-lake")).to_equal("x86_64-apollo-lake")
expect(simpleos_board_has_qemu_id("up-squared-apollo-lake")).to_equal(false)
expect(simpleos_board_physical_script("up-squared-apollo-lake")).to_equal("scripts/os/run_simpleos_up_squared_apl.shs")
val up2_cmd = simpleos_board_physical_build_only_command_for_id_with_mode("up-squared-apollo-lake", SimpleOsProtectionMode.Enforce)
expect(up2_cmd).to_equal(["sh", "scripts/os/run_simpleos_up_squared_apl.shs", "--build-only", "--protection=enforce"])
expect(simpleos_board_protection_marker_for_id("up-squared-apollo-lake", SimpleOsProtectionMode.Enforce)).to_contain("kind=x86-paging-iommu")
val ra_cmd = simpleos_board_physical_build_only_command_for_id_with_mode("ra4m1-uno-r4", SimpleOsProtectionMode.FaultTest)
expect(ra_cmd).to_equal(["sh", "scripts/run_simpleos_ra4m1.shs", "--build-only", "--protection=fault-test"])
val u585_cmd = simpleos_board_physical_build_only_command_for_id_with_mode("stm32u585-uno-q", SimpleOsProtectionMode.Enforce)
expect(u585_cmd).to_equal(["sh", "scripts/run_simpleos_stm32u585.shs", "--build-only", "--protection=enforce"])
val serial_cmd = simpleos_board_physical_serial_check_command_for_id_with_mode(
    "stm32u585-uno-q",
    SimpleOsProtectionMode.FaultTest,
    "build/serial/u585.log"
)
expect(serial_cmd).to_equal([
    "bin/release/x86_64-unknown-linux-gnu/simple",
    "run",
    "src/app/simpleos_board_serial_check/main.spl",
    "--board", "stm32u585-uno-q",
    "--mode", "fault-test",
    "--serial-log", "build/serial/u585.log"
])
expect(simpleos_board_protection_marker_for_id("ra4m1-uno-r4", SimpleOsProtectionMode.Enforce)).to_contain("kind=pmsav7-mpu")
expect(simpleos_board_protection_marker_for_id("stm32u585-uno-q", SimpleOsProtectionMode.Enforce)).to_contain("kind=pmsav8-mpu")
expect(simpleos_board_qemu_command_for_id("ra4m1-uno-r4", "ignored").len()).to_equal(0)

expect(simpleos_board_supports_protection_mode_id("stm32u585-uno-q", SimpleOsProtectionMode.Off)).to_equal(true)
expect(simpleos_board_supports_protection_mode_id("stm32u585-uno-q", SimpleOsProtectionMode.Detect)).to_equal(true)
expect(simpleos_board_supports_protection_mode_id("stm32u585-uno-q", SimpleOsProtectionMode.Enforce)).to_equal(true)
expect(simpleos_board_supports_protection_mode_id("stm32u585-uno-q", SimpleOsProtectionMode.FaultTest)).to_equal(true)
val marker = simpleos_board_protection_marker_for_id("stm32u585-uno-q", SimpleOsProtectionMode.FaultTest)
expect(marker).to_contain("board=stm32u585-uno-q")
expect(marker).to_contain("protection=fault-test")
expect(marker).to_contain("kind=pmsav8-mpu")
```

</details>

#### requires runtime evidence before protection modes satisfy acceptance

- requires runtime evidence before protection modes satisfy acceptance
   - Expected: simpleos_protection_evidence_ready(unchecked) is false
   - Expected: simpleos_protection_evidence_reason(unchecked) equals `missing-runtime-check`
   - Expected: simpleos_protection_evidence_ready(detect) is true
   - Expected: simpleos_protection_evidence_accepts_hardening(detect) is false
   - Expected: simpleos_protection_evidence_reason(enforce_missing_regions) equals `missing-region-contract`
   - Expected: simpleos_protection_evidence_reason(fault_missing_recovery) equals `missing-fault-recovery`
   - Expected: simpleos_protection_evidence_ready(fault_ready) is true
   - Expected: simpleos_protection_evidence_accepts_hardening(fault_ready) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 70 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires runtime evidence before protection modes satisfy acceptance")
val unchecked = simpleos_protection_evidence(
    "mps2-an505",
    SimpleOsProtectionMode.Enforce,
    true,
    true,
    true,
    true,
    false,
    false,
    false
)
expect(simpleos_protection_evidence_ready(unchecked)).to_equal(false)
expect(simpleos_protection_evidence_reason(unchecked)).to_equal("missing-runtime-check")

val detect = simpleos_protection_evidence(
    "mps2-an505",
    SimpleOsProtectionMode.Detect,
    true,
    true,
    false,
    false,
    false,
    true,
    false
)
expect(simpleos_protection_evidence_ready(detect)).to_equal(true)
expect(simpleos_protection_evidence_accepts_hardening(detect)).to_equal(false)
expect(simpleos_protection_evidence_marker(detect)).to_contain("runtime=qemu")

val enforce_missing_regions = simpleos_protection_evidence(
    "x86_64-q35",
    SimpleOsProtectionMode.Enforce,
    true,
    true,
    true,
    false,
    false,
    true,
    false
)
expect(simpleos_protection_evidence_reason(enforce_missing_regions)).to_equal("missing-region-contract")

val fault_missing_recovery = simpleos_protection_evidence(
    "ra4m1-uno-r4",
    SimpleOsProtectionMode.FaultTest,
    true,
    true,
    true,
    true,
    false,
    false,
    true
)
expect(simpleos_protection_evidence_reason(fault_missing_recovery)).to_equal("missing-fault-recovery")

val fault_ready = simpleos_protection_evidence(
    "stm32u585-uno-q",
    SimpleOsProtectionMode.FaultTest,
    true,
    true,
    true,
    true,
    true,
    false,
    true
)
expect(simpleos_protection_evidence_ready(fault_ready)).to_equal(true)
expect(simpleos_protection_evidence_accepts_hardening(fault_ready)).to_equal(true)
```

</details>

#### classifies protection evidence from serial markers

- classifies protection evidence from serial markers
   - Expected: simpleos_serial_has_protection_probe(an505_serial) is true
   - Expected: simpleos_serial_has_protection_kind_contract("mps2-an505", an505_serial) is true
   - Expected: simpleos_serial_has_protection_enabled(an505_serial) is true
   - Expected: simpleos_serial_has_region_contract(an505_serial) is true
   - Expected: simpleos_serial_has_fault_recovery(an505_serial) is false
   - Expected: simpleos_protection_evidence_ready(an505_evidence) is true
   - Expected: simpleos_protection_evidence_accepts_hardening(an505_evidence) is true
   - Expected: simpleos_protection_evidence_ready(fault_evidence) is true
   - Expected: simpleos_protection_evidence_accepts_hardening(fault_evidence) is true
   - Expected: simpleos_serial_has_protection_kind_contract("stm32u585-uno-q", wrong_kind_serial) is false
   - Expected: simpleos_protection_evidence_reason(wrong_kind) equals `missing-protection-kind-contract:pmsav8-mpu`
   - Expected: simpleos_protection_evidence_ready(x86_evidence) is true
   - Expected: simpleos_protection_evidence_reason(no_runtime) equals `missing-runtime-check`


<details>
<summary>Executable SSpec</summary>

Runnable source: 56 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies protection evidence from serial markers")
val an505_serial = "[BOOT] Platform: MPS2-AN505 (QEMU)\n[FAULT] MemManage, BusFault, UsageFault enabled; DIV0 trap on\n[MPU] Enabled, 8 regions available, 4 configured\n[BOOT] Entering shell..."
expect(simpleos_serial_has_protection_probe(an505_serial)).to_equal(true)
expect(simpleos_serial_has_protection_kind_contract("mps2-an505", an505_serial)).to_equal(true)
expect(simpleos_serial_has_protection_enabled(an505_serial)).to_equal(true)
expect(simpleos_serial_has_region_contract(an505_serial)).to_equal(true)
expect(simpleos_serial_has_fault_recovery(an505_serial)).to_equal(false)

val an505_evidence = simpleos_protection_evidence_from_serial(
    "mps2-an505",
    SimpleOsProtectionMode.Enforce,
    "qemu",
    an505_serial
)
expect(simpleos_protection_evidence_ready(an505_evidence)).to_equal(true)
expect(simpleos_protection_evidence_accepts_hardening(an505_evidence)).to_equal(true)
expect(simpleos_protection_evidence_marker(an505_evidence)).to_contain("runtime=qemu")

val explicit_fault_serial = "protection=fault-test\nkind=pmsav8-mpu\nprotection_probe=pass\nprotection_enabled=pass\nregion_contract=pass\nfault_recovered=pass\nTEST PASSED"
val fault_evidence = simpleos_protection_evidence_from_serial(
    "stm32u585-uno-q",
    SimpleOsProtectionMode.FaultTest,
    "real-board",
    explicit_fault_serial
)
expect(simpleos_protection_evidence_ready(fault_evidence)).to_equal(true)
expect(simpleos_protection_evidence_accepts_hardening(fault_evidence)).to_equal(true)
expect(simpleos_protection_evidence_marker(fault_evidence)).to_contain("runtime=real-board")

val wrong_kind_serial = "protection=fault-test\nkind=pmsav7-mpu\nprotection_probe=pass\nprotection_enabled=pass\nregion_contract=pass\nfault_recovered=pass\n"
val wrong_kind = simpleos_protection_evidence_from_serial(
    "stm32u585-uno-q",
    SimpleOsProtectionMode.FaultTest,
    "real-board",
    wrong_kind_serial
)
expect(simpleos_serial_has_protection_kind_contract("stm32u585-uno-q", wrong_kind_serial)).to_equal(false)
expect(simpleos_protection_evidence_reason(wrong_kind)).to_equal("missing-protection-kind-contract:pmsav8-mpu")

val x86_serial = "[BOOT64] call _start\n[harden] text_write_trap=pass\nTEST PASSED"
val x86_evidence = simpleos_protection_evidence_from_serial(
    "x86_64-q35",
    SimpleOsProtectionMode.Enforce,
    "qemu",
    x86_serial
)
expect(simpleos_protection_evidence_ready(x86_evidence)).to_equal(true)

val no_runtime = simpleos_protection_evidence_from_serial(
    "mps2-an505",
    SimpleOsProtectionMode.Enforce,
    "none",
    an505_serial
)
expect(simpleos_protection_evidence_reason(no_runtime)).to_equal("missing-runtime-check")
```

</details>

#### checks physical serial logs with real-board evidence semantics

- checks physical serial logs with real-board evidence semantics
   - Expected: simpleos_physical_serial_accepts_hardening("stm32u585-uno-q", "fault-test", ready) is true
   - Expected: simpleos_physical_serial_acceptance_reason("stm32u585-uno-q", "fault-test", ready) equals `ready`
   - Expected: simpleos_physical_serial_acceptance_reason("stm32u585-uno-q", "fault-test", no_mode) equals `missing-physical-board-marker:stm32u585-uno-q`
   - Expected: simpleos_serial_has_selected_protection_mode(SimpleOsProtectionMode.FaultTest, no_mode_with_board) is false
   - Expected: simpleos_physical_serial_acceptance_reason("stm32u585-uno-q", "fault-test", no_mode_with_board) equals `missing-selected-protection-mode:fault-test`
   - Expected: simpleos_physical_serial_acceptance_reason("stm32u585-uno-q", "fault-test", build_only) equals `real-board-not-run`
   - Expected: simpleos_physical_serial_acceptance_reason("stm32u585-uno-q", "fault-test", wrong_board) equals `missing-physical-board-marker:stm32u585-uno-q`
   - Expected: simpleos_physical_serial_acceptance_reason("ra4m1-uno-r4", "detect", diagnostic) equals `diagnostic-protection-mode:detect`
   - Expected: simpleos_physical_serial_acceptance_reason("mps2-an505", "enforce", ready) equals `missing-physical-board-script:mps2-an505`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks physical serial logs with real-board evidence semantics")
val ready = "board=stm32u585-uno-q\nprotection=fault-test\nkind=pmsav8-mpu\nprotection_probe=pass\nprotection_enabled=pass\nregion_contract=pass\nfault_recovered=pass\n"
expect(simpleos_physical_serial_accepts_hardening("stm32u585-uno-q", "fault-test", ready)).to_equal(true)
expect(simpleos_physical_serial_acceptance_reason("stm32u585-uno-q", "fault-test", ready)).to_equal("ready")

val no_mode = "kind=pmsav8-mpu\nprotection_probe=pass\nprotection_enabled=pass\nregion_contract=pass\nfault_recovered=pass\n"
expect(simpleos_physical_serial_acceptance_reason("stm32u585-uno-q", "fault-test", no_mode)).to_equal("missing-physical-board-marker:stm32u585-uno-q")

val no_mode_with_board = "board=stm32u585-uno-q\nkind=pmsav8-mpu\nprotection_probe=pass\nprotection_enabled=pass\nregion_contract=pass\nfault_recovered=pass\n"
expect(simpleos_serial_has_selected_protection_mode(SimpleOsProtectionMode.FaultTest, no_mode_with_board)).to_equal(false)
expect(simpleos_physical_serial_acceptance_reason("stm32u585-uno-q", "fault-test", no_mode_with_board)).to_equal("missing-selected-protection-mode:fault-test")

val build_only = "[u585] REAL_BOARD_NOT_RUN board=stm32u585-uno-q reason=build-only protection=fault-test\n"
expect(simpleos_physical_serial_acceptance_reason("stm32u585-uno-q", "fault-test", build_only)).to_equal("real-board-not-run")

val wrong_board = "board=ra4m1-uno-r4\nprotection=fault-test\nkind=pmsav8-mpu\nprotection_probe=pass\nprotection_enabled=pass\nregion_contract=pass\nfault_recovered=pass\n"
expect(simpleos_physical_serial_acceptance_reason("stm32u585-uno-q", "fault-test", wrong_board)).to_equal("missing-physical-board-marker:stm32u585-uno-q")

val diagnostic = "board=ra4m1-uno-r4\nprotection=detect\nkind=pmsav7-mpu\nprotection_probe=pass\n"
expect(simpleos_physical_serial_acceptance_reason("ra4m1-uno-r4", "detect", diagnostic)).to_equal("diagnostic-protection-mode:detect")
expect(simpleos_physical_serial_acceptance_reason("mps2-an505", "enforce", ready)).to_equal("missing-physical-board-script:mps2-an505")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/simpleos_board_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS board hardening catalog.
- SimpleOS board hardening catalog

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `d24d6bf697b7faf7c48ee3b0f78ab1829f14d1160fa25e97c7a3409f5d3931a7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d24d6bf697b7faf7c48ee3b0f78ab1829f14d1160fa25e97c7a3409f5d3931a7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d24d6bf697b7faf7c48ee3b0f78ab1829f14d1160fa25e97c7a3409f5d3931a7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/simpleos_board_hardening_spec.spl
mirror: doc/06_spec/unit/os/simpleos_board_hardening_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/simpleos_board_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/simpleos_board_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/simpleos_board_hardening_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/simpleos_board_hardening_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines optional protection modes and real board/QEMU contracts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/simpleos_board_hardening_spec.spl:214:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies protection evidence from serial markers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/simpleos_board_hardening_spec.spl:272:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks physical serial logs with real-board evidence semantics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
