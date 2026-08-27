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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Executable trace for the historical RV64 Linux platform contract that now feeds the dual-arch generated Linux truth model.

## Scenarios

### REQ-RV64-LINUX-RTL-001..005: historical RV64 platform contract within the dual-arch model

#### defines one RV64 QEMU virt Linux contract used by the shared dual-arch pipeline

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-RV64-LINUX-RTL-001..005
# @req REQ-RV64-LINUX-RTL-006..010
```

</details>

#### requires firmware, kernel, rootfs, and dtb for RV64 Linux boot claims

- requires firmware, kernel, rootfs, and dtb for RV64 Linux boot claims


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires firmware, kernel, rootfs, and dtb for RV64 Linux boot claims")
val artifacts = Rv64LinuxBootArtifacts.empty()
val errors = artifacts.validate_for(RiscvPlatformProfile.qemu_virt_rv64().linux)
expect(errors).to_contain("kernel_image is required")
expect(errors).to_contain("initrd_rootfs is required")
expect(errors).to_contain("dtb is required")
expect(errors).to_contain("OpenSBI or U-Boot firmware is required")
```

</details>

#### keeps generated and external RV64 Linux proof lanes distinct in repo manifests

- keeps generated and external RV64 Linux proof lanes distinct in repo manifests
   - Expected: lane.proof_lane().to_text() equals `generated_rv64_linux`
   - Expected: lane.proof_lane_summary() equals `generated_rv64_linux shell=none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps generated and external RV64 Linux proof lanes distinct in repo manifests")
val lane = RiscvFpgaLane.rv64_default()
val manifest = create_default_riscv_fpga_linux_manifest()
expect(lane.proof_lane().to_text()).to_equal("generated_rv64_linux")
expect(lane.proof_lane_summary()).to_equal("generated_rv64_linux shell=none")
expect(manifest.readiness_summary()).to_contain("generated_rv64_linux")
```

</details>

#### defines rtl-linux-validated as a generated Linux boot claim state

- defines rtl-linux-validated as a generated Linux boot claim state
   - Expected: lane.readiness_is_boot_validated() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines rtl-linux-validated as a generated Linux boot claim state")
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

- defines explicit RV64 Linux compiler metadata
   - Expected: contract.triple() equals `riscv64-unknown-linux-gnu`
   - Expected: contract.abi.to_text() equals `lp64d`
   - Expected: contract.march equals `rv64gc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines explicit RV64 Linux compiler metadata")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-RV64-LINUX-RTL-001..005`
- `REQ-RV64-LINUX-RTL-006..010`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a0e444ccbbb839e031991236b333baa8365e1c8e3d9b342a7939a4084a9099b6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a0e444ccbbb839e031991236b333baa8365e1c8e3d9b342a7939a4084a9099b6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a0e444ccbbb839e031991236b333baa8365e1c8e3d9b342a7939a4084a9099b6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/app/hardware/feature/rv64_linux_rtl_pipeline_spec.spl
mirror: doc/06_spec/03_system/app/hardware/feature/rv64_linux_rtl_pipeline_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/hardware/feature/rv64_linux_rtl_pipeline_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/hardware/feature/rv64_linux_rtl_pipeline_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/hardware/feature/rv64_linux_rtl_pipeline_spec.spl:21:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'defines one RV64 QEMU virt Linux contract used by the shared dual-arch pipeline' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/hardware/feature/rv64_linux_rtl_pipeline_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires firmware, kernel, rootfs, and dtb for RV64 Linux boot claims' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/hardware/feature/rv64_linux_rtl_pipeline_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps generated and external RV64 Linux proof lanes distinct in repo manifests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/hardware/feature/rv64_linux_rtl_pipeline_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines rtl-linux-validated as a generated Linux boot claim state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
