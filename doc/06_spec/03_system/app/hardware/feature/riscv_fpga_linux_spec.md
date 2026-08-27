# RISC-V FPGA Linux System Specification

> Executable requirement trace for the dual-arch orchestration layer.

<!-- sdn-diagram:id=riscv_fpga_linux_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv_fpga_linux_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv_fpga_linux_spec -> std
riscv_fpga_linux_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv_fpga_linux_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RISC-V FPGA Linux System Specification

Executable requirement trace for the dual-arch orchestration layer.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/hardware/feature/riscv_fpga_linux_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Executable requirement trace for the dual-arch orchestration layer.

## Scenarios

### REQ-RFL-001..003: board and lane contracts

#### keeps board validation separate from hardware boot validation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = XilinxBoardProfile.generic()
expect(profile.validate_for_prepare().len()).to_equal(0)
expect(profile.validate_for_hardware_boot()).to_contain("xilinx part must be selected before hardware boot")
```

</details>

#### publishes MLK-S02-100T as a named board profile with concrete part, clock, and programmer

- publishes MLK-S02-100T as a named board profile with concrete part, clock, and programmer
   - Expected: mlk.part equals `xc7a100tfgg484-2`
   - Expected: mlk.clock_hz equals `25000000`
   - Expected: mlk.programmer equals `openFPGALoader`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("publishes MLK-S02-100T as a named board profile with concrete part, clock, and programmer")
val mlk = XilinxBoardProfile.from_id("mlk_s02_100t").ok().unwrap()
expect(mlk.part).to_equal("xc7a100tfgg484-2")
expect(mlk.clock_hz).to_equal(25000000)
expect(mlk.programmer).to_equal("openFPGALoader")
```

</details>

#### defines both RV32 and RV64 as generated Linux lanes

- defines both RV32 and RV64 as generated Linux lanes
   - Expected: rv32.readiness_status() equals `RiscvReadinessStatus.Contract`
   - Expected: rv32.proof_lane().to_text() equals `generated_rv32_linux`
   - Expected: rv32.xlen.linux_policy() equals `repo-native-rv32-linux`
   - Expected: rv64.proof_lane().to_text() equals `generated_rv64_linux`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines both RV32 and RV64 as generated Linux lanes")
val rv32 = RiscvFpgaLane.rv32_default()
val rv64 = RiscvFpgaLane.rv64_default()
expect(rv32.readiness_status()).to_equal(RiscvReadinessStatus.Contract)
expect(rv32.proof_lane().to_text()).to_equal("generated_rv32_linux")
expect(rv32.xlen.linux_policy()).to_equal("repo-native-rv32-linux")
expect(rv64.proof_lane().to_text()).to_equal("generated_rv64_linux")
```

</details>

### REQ-RFL-004..006: deterministic dual-arch orchestration

#### creates a deterministic default dual-arch manifest

- creates a deterministic default dual-arch manifest
   - Expected: manifest.lanes.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates a deterministic default dual-arch manifest")
val manifest = create_default_riscv_fpga_linux_manifest()
expect(manifest.lanes.len()).to_equal(2)
expect(manifest.readiness_summary()).to_contain("rv32:contract:qemu_virt_rv32")
expect(manifest.readiness_summary()).to_contain("rv64:contract:qemu_virt_rv64")
```

</details>

#### creates board-specific manifests and per-arch boot products for MLK-S02-100T

- creates board-specific manifests and per-arch boot products for MLK-S02-100T
   - Expected: manifest.board.name equals `mlk_s02_100t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates board-specific manifests and per-arch boot products for MLK-S02-100T")
val manifest = create_riscv_fpga_linux_manifest_for_board("mlk_s02_100t").ok().unwrap()
expect(manifest.board.name).to_equal("mlk_s02_100t")
expect(manifest.vivado_tcl_plan()).to_contain("examples/09_embedded/fpga_riscv/constraints/mlk_s02_100t.xdc")
val products = manifest.board_linux_boot_products_manifest_text("/tmp/simple_riscv_fpga_system_spec_mlk")
expect(products).to_contain("product_id = \"mlk_s02_100t_rv32_linux\"")
expect(products).to_contain("product_id = \"mlk_s02_100t_rv64_linux\"")
expect(products).to_contain("boot_script = \"scripts/mlk_s02_100t_generated_linux_boot.shs\"")
expect(products).to_contain("validation_kind = \"linux-uart-markers\"")
```

</details>

#### emits generated bundle metadata and a boot products manifest

- emits generated bundle metadata and a boot products manifest
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 79 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("emits generated bundle metadata and a boot products manifest")
val result = generate_default_riscv_fpga_rtl_bundle("/tmp/simple_riscv_fpga_system_spec")
expect(result.is_ok()).to_equal(true)
val bundle = result.ok().unwrap()
val manifest_text = read_generated_riscv_fpga_rtl_file(bundle.manifest_path)
val products_text = read_generated_riscv_fpga_rtl_file(bundle.board_linux_boot_products_manifest_path)
val bundle_readme_text = read_generated_riscv_fpga_rtl_file(bundle.bundle_readme_path)
expect(manifest_text).to_contain("proof_lane = \"generated_rv32_linux\"")
expect(manifest_text).to_contain("proof_lane = \"generated_rv64_linux\"")
expect(manifest_text).to_contain("authoritative_rtl_provenance = \"simple-compiler-generated\"")
expect(manifest_text).to_contain("authoritative_file = \"/tmp/simple_riscv_fpga_system_spec/rv32/rtl/simple_rv32gc_core.spl\"")
expect(manifest_text).to_contain("authoritative_file = \"/tmp/simple_riscv_fpga_system_spec/rv64/rtl/simple_rv64gc_core.vhd\"")
expect(manifest_text).to_contain("pure_simple_authoritative_rtl = \"true\"")
expect(products_text).to_contain("product_id = \"xilinx_generic_rv32_linux\"")
expect(products_text).to_contain("product_id = \"xilinx_generic_rv64_linux\"")
expect(products_text).to_contain("expected_markers = \"OpenSBI|Linux version|OF: fdt|Freeing unused kernel memory|init started\"")
expect(bundle_readme_text).to_contain("per-arch boot products manifest: `board_linux_boot_products.sdn`")
expect(bundle_readme_text).to_contain("The machine-readable authoritative subset is listed explicitly by `authoritative_file` entries in the manifest and `provenance.authoritativeFiles` in the debug sidecar.")
```

</details>

#### emits MLK-specific bundle metadata for board-level hardware wrappers

- emits MLK-specific bundle metadata for board-level hardware wrappers
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("emits MLK-specific bundle metadata for board-level hardware wrappers")
val result = generate_riscv_fpga_rtl_bundle_for_board("/tmp/simple_riscv_fpga_system_spec_mlk", "mlk_s02_100t")
expect(result.is_ok()).to_equal(true)
val bundle = result.ok().unwrap()
val manifest_text = read_generated_riscv_fpga_rtl_file(bundle.manifest_path)
val products_text = read_generated_riscv_fpga_rtl_file(bundle.board_linux_boot_products_manifest_path)
expect(manifest_text).to_contain("board = \"mlk_s02_100t\"")
expect(products_text).to_contain("product_id = \"mlk_s02_100t_rv32_linux\"")
expect(products_text).to_contain("product_id = \"mlk_s02_100t_rv64_linux\"")
```

</details>

#### propagates a custom configuration profile into manifest and sidecars

- propagates a custom configuration profile into manifest and sidecars
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("propagates a custom configuration profile into manifest and sidecars")
val result = generate_riscv_fpga_rtl_bundle_for_board_with_profile("/tmp/simple_riscv_fpga_system_spec_custom_profile", "mlk_s02_100t", "mlk-s02-100t+formal")
expect(result.is_ok()).to_equal(true)
val bundle = result.ok().unwrap()
val manifest_text = read_generated_riscv_fpga_rtl_file(bundle.manifest_path)
val rv32_sidecar = read_generated_riscv_fpga_rtl_file("/tmp/simple_riscv_fpga_system_spec_custom_profile/rv32/rtl/simple_rv32gc_core.debug.json")
val rv64_sidecar = read_generated_riscv_fpga_rtl_file("/tmp/simple_riscv_fpga_system_spec_custom_profile/rv64/rtl/simple_rv64gc_core.debug.json")
expect(manifest_text).to_contain("configuration_profile = \"mlk-s02-100t+formal\"")
expect(rv32_sidecar).to_contain("\"configurationProfile\": \"mlk-s02-100t+formal\"")
expect(rv64_sidecar).to_contain("\"configurationProfile\": \"mlk-s02-100t+formal\"")
```

</details>

#### propagates custom product level, RTL size, and performance budgets into manifest and sidecars

- propagates custom product level, RTL size, and performance budgets into manifest and sidecars
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("propagates custom product level, RTL size, and performance budgets into manifest and sidecars")
val result = generate_riscv_fpga_rtl_bundle_configured("/tmp/simple_riscv_fpga_system_spec_custom_budget", "mlk_s02_100t", "lab-rtl", "budget-check", 21000, 39000, 75, 80)
expect(result.is_ok()).to_equal(true)
val bundle = result.ok().unwrap()
val manifest_text = read_generated_riscv_fpga_rtl_file(bundle.manifest_path)
val byl_text = read_generated_riscv_fpga_rtl_file("/tmp/simple_riscv_fpga_system_spec_custom_budget/riscv_product.byl")
val rv32_synth_template = read_generated_riscv_fpga_rtl_file("/tmp/simple_riscv_fpga_system_spec_custom_budget/synth/rv32_synth.sdn")
val rv64_synth_template = read_generated_riscv_fpga_rtl_file("/tmp/simple_riscv_fpga_system_spec_custom_budget/synth/rv64_synth.sdn")
val rv32_sidecar = read_generated_riscv_fpga_rtl_file("/tmp/simple_riscv_fpga_system_spec_custom_budget/rv32/rtl/simple_rv32gc_core.debug.json")
val rv64_sidecar = read_generated_riscv_fpga_rtl_file("/tmp/simple_riscv_fpga_system_spec_custom_budget/rv64/rtl/simple_rv64gc_core.debug.json")
expect(manifest_text).to_contain("product_level = \"lab-rtl\"")
expect(manifest_text).to_contain("rtl_size_budget_luts = \"21000\"")
expect(manifest_text).to_contain("rtl_size_budget_luts = \"39000\"")
expect(manifest_text).to_contain("perf_target_mhz = \"75\"")
expect(manifest_text).to_contain("perf_target_mhz = \"80\"")
expect(byl_text).to_contain("product_level = \"lab-rtl\"")
expect(byl_text).to_contain("configuration_profile = \"budget-check\"")
expect(byl_text).to_contain("max_luts = 21000")
expect(byl_text).to_contain("target_mhz = 80")
expect(rv32_synth_template).to_contain("max_luts = 21000")
expect(rv32_synth_template).to_contain("target_mhz = 75")
expect(rv64_synth_template).to_contain("max_luts = 39000")
expect(rv64_synth_template).to_contain("target_mhz = 80")
expect(rv32_sidecar).to_contain("\"productLevel\": \"lab-rtl\"")
expect(rv32_sidecar).to_contain("\"rtlBudget\": {\"maxLuts\": 21000, \"targetMhz\": 75}")
expect(rv64_sidecar).to_contain("\"productLevel\": \"lab-rtl\"")
expect(rv64_sidecar).to_contain("\"rtlBudget\": {\"maxLuts\": 39000, \"targetMhz\": 80}")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-RFL-001..003`
- `REQ-RFL-004..006`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `10fbbda8606d0486b458605e0f9a0499cc0cba6fcad3159283b42ba540dd51b1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `10fbbda8606d0486b458605e0f9a0499cc0cba6fcad3159283b42ba540dd51b1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `10fbbda8606d0486b458605e0f9a0499cc0cba6fcad3159283b42ba540dd51b1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/03_system/app/hardware/feature/riscv_fpga_linux_spec.spl
mirror: doc/06_spec/03_system/app/hardware/feature/riscv_fpga_linux_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/hardware/feature/riscv_fpga_linux_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/hardware/feature/riscv_fpga_linux_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/hardware/feature/riscv_fpga_linux_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/hardware/feature/riscv_fpga_linux_spec.spl:19:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'keeps board validation separate from hardware boot validation' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/hardware/feature/riscv_fpga_linux_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes MLK-S02-100T as a named board profile with concrete part, clock, and programmer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/hardware/feature/riscv_fpga_linux_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines both RV32 and RV64 as generated Linux lanes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/hardware/feature/riscv_fpga_linux_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a deterministic default dual-arch manifest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
