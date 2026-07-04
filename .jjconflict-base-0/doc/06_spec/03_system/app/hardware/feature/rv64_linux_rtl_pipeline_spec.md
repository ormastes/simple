# RV64 Linux RTL Pipeline System Specification

> Executable trace for the historical RV64 Linux platform contract that now feeds the dual-arch generated Linux truth model.

<!-- sdn-diagram:id=rv64_linux_rtl_pipeline_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_linux_rtl_pipeline_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_linux_rtl_pipeline_spec -> hardware
rv64_linux_rtl_pipeline_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_linux_rtl_pipeline_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Executable trace for the historical RV64 Linux platform contract that now feeds the dual-arch generated Linux truth model.

## Scenarios

### REQ-RV64-LINUX-RTL-001..005: historical RV64 platform contract within the dual-arch model

#### defines one RV64 QEMU virt Linux contract used by the shared dual-arch pipeline

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = RiscvPlatformProfile.qemu_virt_rv64()
expect(profile.name).to_equal("qemu_virt_rv64")
expect(profile.linux.abi).to_equal(RiscvTargetAbi.LP64D)
expect(profile.hartid_register).to_equal("a0")
expect(profile.dtb_register).to_equal("a1")
expect(profile.satp_mode_off).to_equal(true)
```

</details>

#### requires firmware, kernel, rootfs, and dtb for RV64 Linux boot claims

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifacts = Rv64LinuxBootArtifacts.empty()
val errors = artifacts.validate_for(RiscvPlatformProfile.qemu_virt_rv64().linux)
expect(errors).to_contain("kernel_image is required")
expect(errors).to_contain("initrd_rootfs is required")
expect(errors).to_contain("dtb is required")
expect(errors).to_contain("OpenSBI or U-Boot firmware is required")
```

</details>

#### keeps generated and external RV64 Linux proof lanes distinct in repo manifests

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lane = RiscvFpgaLane.rv64_default()
val manifest = create_default_riscv_fpga_linux_manifest()
expect(lane.proof_lane().to_text()).to_equal("generated_rv64_linux")
expect(lane.proof_lane_summary()).to_equal("generated_rv64_linux shell=none")
expect(manifest.readiness_summary()).to_contain("generated_rv64_linux")
```

</details>

#### defines rtl-linux-validated as a generated Linux boot claim state

1. xlen: RiscvFpgaLane rv64 default
2. top module: RiscvFpgaLane rv64 default
3. rtl dir: RiscvFpgaLane rv64 default
4. rtl sim backend: RiscvFpgaLane rv64 default
5. bootrom path: RiscvFpgaLane rv64 default
6. linux profile: RiscvFpgaLane rv64 default
7. platform profile: RiscvFpgaLane rv64 default
8. scope note: RiscvFpgaLane rv64 default
9. linux: RiscvFpgaLane rv64 default
   - Expected: lane.readiness_is_boot_validated() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
