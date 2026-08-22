# RV64 Linux RTL Pipeline System Specification

> Executable trace for the historical RV64 Linux platform contract that now feeds the dual-arch generated Linux truth model.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Linux RTL Pipeline System Specification

Executable trace for the historical RV64 Linux platform contract that now feeds the dual-arch generated Linux truth model.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/hardware/feature/rv64_linux_rtl_pipeline_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations

# RV64 Linux RTL Pipeline System Specification

Executable trace for the historical RV64 Linux platform contract that now feeds the dual-arch generated Linux truth model.

## Scenarios

### REQ-RV64-LINUX-RTL-001..005: historical RV64 platform contract within the dual-arch model

#### defines one RV64 QEMU virt Linux contract used by the shared dual-arch pipeline

- Verify: defines one RV64 QEMU virt Linux contract used by the shared dual-arch pipeline
   - Expected: profile.name equals `qemu_virt_rv64`
   - Expected: profile.linux.abi equals `RiscvTargetAbi.LP64D`
   - Expected: profile.hartid_register equals `a0`
   - Expected: profile.dtb_register equals `a1`
   - Expected: profile.satp_mode_off is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV64-LINUX-RTL-001 REQ-RV64-LINUX-RTL-006 REQ-RV64-LINUX-RTL-001..005 REQ-RV64-LINUX-RTL-006..010
step("Verify: defines one RV64 QEMU virt Linux contract used by the shared dual-arch pipeline")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val profile = RiscvPlatformProfile.qemu_virt_rv64()
expect(profile.name).to_equal("qemu_virt_rv64")
expect(profile.linux.abi).to_equal(RiscvTargetAbi.LP64D)
expect(profile.hartid_register).to_equal("a0")
expect(profile.dtb_register).to_equal("a1")
expect(profile.satp_mode_off).to_equal(true)
```

</details>

#### requires firmware, kernel, rootfs, and dtb for RV64 Linux boot claims

- Verify: requires firmware, kernel, rootfs, and dtb for RV64 Linux boot claims


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV64-LINUX-RTL-001 REQ-RV64-LINUX-RTL-006
step("Verify: requires firmware, kernel, rootfs, and dtb for RV64 Linux boot claims")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val artifacts = Rv64LinuxBootArtifacts.empty()
val errors = artifacts.validate_for(RiscvPlatformProfile.qemu_virt_rv64().linux)
expect(errors).to_contain("kernel_image is required")
expect(errors).to_contain("initrd_rootfs is required")
expect(errors).to_contain("dtb is required")
expect(errors).to_contain("OpenSBI or U-Boot firmware is required")
```

</details>

#### keeps generated and external RV64 Linux proof lanes distinct in repo manifests

- Verify: keeps generated and external RV64 Linux proof lanes distinct in repo manifests
   - Expected: lane.proof_lane().to_text() equals `generated_rv64_linux`
   - Expected: lane.proof_lane_summary() equals `generated_rv64_linux shell=none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV64-LINUX-RTL-001 REQ-RV64-LINUX-RTL-006
step("Verify: keeps generated and external RV64 Linux proof lanes distinct in repo manifests")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val lane = RiscvFpgaLane.rv64_default()
val manifest = create_default_riscv_fpga_linux_manifest()
expect(lane.proof_lane().to_text()).to_equal("generated_rv64_linux")
expect(lane.proof_lane_summary()).to_equal("generated_rv64_linux shell=none")
expect(manifest.readiness_summary()).to_contain("generated_rv64_linux")
```

</details>

#### defines rtl-linux-validated as a generated Linux boot claim state

- Verify: defines rtl-linux-validated as a generated Linux boot claim state
   - Expected: lane.readiness_is_boot_validated() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV64-LINUX-RTL-001 REQ-RV64-LINUX-RTL-006
step("Verify: defines rtl-linux-validated as a generated Linux boot claim state")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val lane = RiscvFpgaLane(
    xlen: RiscvFpgaLane.rv64_default().xlen,
    top_module: RiscvFpgaLane.rv64_default().top_module,
    rtl_dir: RiscvFpgaLane.rv64_default().rtl_dir,
    rtl_sim_backend: RiscvFpgaLane.rv64_default().rtl_sim_backend,
    bootrom_path: RiscvFpgaLane.rv64_default().bootrom_path,
    readiness: RiscvReadinessStatus.RtlLinuxValidated,
    linux_profile: RiscvFpgaLane.rv64_default().linux_profile,
    platform_profile: RiscvFpgaLane.rv64_default().platform_profile,
    scope_note: RiscvFpgaLane.rv64_default().scope_note,
    linux: RiscvFpgaLane.rv64_default().linux
)
expect(lane.readiness_is_boot_validated()).to_equal(true)
expect(lane.expected_boot_markers()).to_contain("Linux version")
```

</details>

### REQ-RV64-LINUX-RTL-006..010: compiler backend trace

#### defines explicit RV64 Linux compiler metadata

- Verify: defines explicit RV64 Linux compiler metadata
   - Expected: contract.triple() equals `riscv64-unknown-linux-gnu`
   - Expected: contract.abi.to_text() equals `lp64d`
   - Expected: contract.march equals `rv64gc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV64-LINUX-RTL-001 REQ-RV64-LINUX-RTL-006
step("Verify: defines explicit RV64 Linux compiler metadata")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val contract = riscv_linux_target_contract(CodegenTarget.Riscv64)
expect(contract.triple()).to_equal("riscv64-unknown-linux-gnu")
expect(contract.abi.to_text()).to_equal("lp64d")
expect(contract.march).to_equal("rv64gc")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bb058c295b4f7f99f0e481f3b5e13e92a6eee55621cd8cca4f8ed97128234597`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bb058c295b4f7f99f0e481f3b5e13e92a6eee55621cd8cca4f8ed97128234597`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bb058c295b4f7f99f0e481f3b5e13e92a6eee55621cd8cca4f8ed97128234597`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/hardware/feature/rv64_linux_rtl_pipeline_spec.spl
mirror: doc/06_spec/03_system/app/hardware/feature/rv64_linux_rtl_pipeline_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/hardware/feature/rv64_linux_rtl_pipeline_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/hardware/feature/rv64_linux_rtl_pipeline_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/hardware/feature/rv64_linux_rtl_pipeline_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
