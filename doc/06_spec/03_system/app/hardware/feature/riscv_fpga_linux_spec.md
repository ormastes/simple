# RISC-V FPGA Linux System Specification

> Executable requirement trace for the dual-arch orchestration layer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

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
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations

# RISC-V FPGA Linux System Specification

Executable requirement trace for the dual-arch orchestration layer.

## Scenarios

### REQ-RFL-001..003: board and lane contracts

#### keeps board validation separate from hardware boot validation

- Verify: keeps board validation separate from hardware boot validation
   - Expected: profile.validate_for_prepare().len() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RFL-001 REQ-RFL-004 REQ-RFL-001..003 REQ-RFL-004..006
step("Verify: keeps board validation separate from hardware boot validation")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val profile = XilinxBoardProfile.generic()
expect(profile.validate_for_prepare().len()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(profile.validate_for_hardware_boot()).to_contain("xilinx part must be selected before hardware boot")
```

</details>

#### publishes MLK-S02-100T as a named board profile with concrete part, clock, and programmer

- Verify: publishes MLK-S02-100T as a named board profile with concrete part, clock, and programmer
   - Expected: mlk.part equals `xc7a100tfgg484-2`
   - Expected: mlk.clock_hz equals `25000000)  # oracle: pinned constant asserted by this scenario  # oracle: pin... (full value in folded executable source)`
   - Expected: mlk.programmer equals `openFPGALoader`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RFL-001 REQ-RFL-004 REQ-RFL-001..003 REQ-RFL-004..006
step("Verify: publishes MLK-S02-100T as a named board profile with concrete part, clock, and programmer")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val mlk = XilinxBoardProfile.from_id("mlk_s02_100t").ok().unwrap()
expect(mlk.part).to_equal("xc7a100tfgg484-2")
expect(mlk.clock_hz).to_equal(25000000)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(mlk.programmer).to_equal("openFPGALoader")
```

</details>

#### defines both RV32 and RV64 as generated Linux lanes

- Verify: defines both RV32 and RV64 as generated Linux lanes
   - Expected: rv32.readiness_status() equals `RiscvReadinessStatus.Contract`
   - Expected: rv32.proof_lane().to_text() equals `generated_rv32_linux`
   - Expected: rv32.xlen.linux_policy() equals `repo-native-rv32-linux`
   - Expected: rv64.proof_lane().to_text() equals `generated_rv64_linux`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RFL-001 REQ-RFL-004 REQ-RFL-001..003 REQ-RFL-004..006
step("Verify: defines both RV32 and RV64 as generated Linux lanes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: creates a deterministic default dual-arch manifest
   - Expected: manifest.lanes.len() equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RFL-001 REQ-RFL-004 REQ-RFL-001..003 REQ-RFL-004..006
step("Verify: creates a deterministic default dual-arch manifest")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val manifest = create_default_riscv_fpga_linux_manifest()
expect(manifest.lanes.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(manifest.readiness_summary()).to_contain("rv32:contract:qemu_virt_rv32")
expect(manifest.readiness_summary()).to_contain("rv64:contract:qemu_virt_rv64")
```

</details>

#### creates board-specific manifests and per-arch boot products for MLK-S02-100T

- Verify: creates board-specific manifests and per-arch boot products for MLK-S02-100T
   - Expected: manifest.board.name equals `mlk_s02_100t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RFL-001 REQ-RFL-004 REQ-RFL-001..003 REQ-RFL-004..006
step("Verify: creates board-specific manifests and per-arch boot products for MLK-S02-100T")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val manifest = create_riscv_fpga_linux_manifest_for_board("mlk_s02_100t").ok().unwrap()
expect(manifest.board.name).to_equal("mlk_s02_100t")
expect(manifest.vivado_tcl_plan()).to_contain("examples/09_embedded/fpga_riscv/constraints/mlk_s02_100t.xdc")
val products = manifest.board_linux_boot_products_manifest_text("/tmp/simple_riscv_fpga_system_spec_mlk")
expect(products).to_contain("product_id = \"mlk_s02_100t_rv32_linux\"")
expect(products).to_contain("product_id = \"mlk_s02_100t_rv64_linux\"")
expect(products).to_contain("boot_script = \"scripts/mlk_s02_100t_generated_linux_boot.shs\"")
expect(products).to_contain("validation_kind = \"contract-not-ready\"")
```

</details>

#### emits generated bundle metadata and a boot products manifest

- Verify: emits generated bundle metadata and a boot products manifest
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 80 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RFL-001 REQ-RFL-004 REQ-RFL-001..003 REQ-RFL-004..006
step("Verify: emits generated bundle metadata and a boot products manifest")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = generate_default_riscv_fpga_rtl_bundle("/tmp/simple_riscv_fpga_system_spec")
expect(result.is_ok()).to_equal(true)
val bundle = result.ok().unwrap()
val manifest_text = read_generated_riscv_fpga_rtl_file(bundle.manifest_path)
val products_text = read_generated_riscv_fpga_rtl_file(bundle.board_linux_boot_products_manifest_path)
val byl_text = read_generated_riscv_fpga_rtl_file("/tmp/simple_riscv_fpga_system_spec/riscv_product.byl")
val rv32_synth_template = read_generated_riscv_fpga_rtl_file("/tmp/simple_riscv_fpga_system_spec/synth/rv32_synth.sdn")
val rv64_synth_template = read_generated_riscv_fpga_rtl_file("/tmp/simple_riscv_fpga_system_spec/synth/rv64_synth.sdn")
val bundle_readme_text = read_generated_riscv_fpga_rtl_file(bundle.bundle_readme_path)
val rv32_sidecar = read_generated_riscv_fpga_rtl_file("/tmp/simple_riscv_fpga_system_spec/rv32/rtl/simple_rv32gc_core.debug.json")
val rv64_sidecar = read_generated_riscv_fpga_rtl_file("/tmp/simple_riscv_fpga_system_spec/rv64/rtl/simple_rv64gc_core.debug.json")
val rv32_core_vhdl = read_generated_riscv_fpga_rtl_file("/tmp/simple_riscv_fpga_system_spec/rv32/rtl/simple_rv32gc_core.vhd")
val rv64_core_vhdl = read_generated_riscv_fpga_rtl_file("/tmp/simple_riscv_fpga_system_spec/rv64/rtl/simple_rv64gc_core.vhd")
val rv32_formal_vhdl = read_generated_riscv_fpga_rtl_file("/tmp/simple_riscv_fpga_system_spec/rv32/rtl/simple_rv32gc_core_formal.vhd")
val rv64_formal_vhdl = read_generated_riscv_fpga_rtl_file("/tmp/simple_riscv_fpga_system_spec/rv64/rtl/simple_rv64gc_core_formal.vhd")
val rv32_sby = read_generated_riscv_fpga_rtl_file("/tmp/simple_riscv_fpga_system_spec/rv32/rtl/simple_rv32gc_core.sby")
val rv64_sby = read_generated_riscv_fpga_rtl_file("/tmp/simple_riscv_fpga_system_spec/rv64/rtl/simple_rv64gc_core.sby")
val rv32_formal_manifest = read_generated_riscv_fpga_rtl_file("/tmp/simple_riscv_fpga_system_spec/rv32/rtl/simple_rv32gc_core_formal.sdn")
val rv64_formal_manifest = read_generated_riscv_fpga_rtl_file("/tmp/simple_riscv_fpga_system_spec/rv64/rtl/simple_rv64gc_core_formal.sdn")
expect(manifest_text).to_contain("proof_lane = \"generated_rv32_linux\"")
expect(manifest_text).to_contain("proof_lane = \"generated_rv64_linux\"")
expect(manifest_text).to_contain("board = \"xilinx_generic\"")
expect(manifest_text).to_contain("readiness = \"contract-not-ready\"")
expect(manifest_text).to_contain("authoritative_rtl_provenance = \"none\"")
expect(manifest_text).to_contain("contract_file = \"/tmp/simple_riscv_fpga_system_spec/rv32/rtl/simple_rv32gc_core.spl\"")
expect(manifest_text).to_contain("contract_file = \"/tmp/simple_riscv_fpga_system_spec/rv64/rtl/simple_rv64gc_core.vhd\"")
expect(manifest_text).to_contain("pure_simple_authoritative_rtl = \"false\"")
expect(products_text).to_contain("product_id = \"xilinx_generic_rv32_linux\"")
expect(products_text).to_contain("product_id = \"xilinx_generic_rv64_linux\"")
expect(products_text).to_contain("expected_markers = \"OpenSBI|Linux version|OF: fdt|Freeing unused kernel memory|init started\"")
expect(byl_text).to_contain("schema = \"simple.riscv_product\"")
expect(byl_text).to_contain("lane rv32")
expect(byl_text).to_contain("readiness = \"contract-not-ready\"")
expect(byl_text).to_contain("formal_gate = \"placeholder-rejected\"")
expect(byl_text).to_contain("max_luts = 25000")
expect(byl_text).to_contain("target_mhz = 50")
expect(rv32_synth_template).to_contain("max_luts = 25000")
expect(rv32_synth_template).to_contain("target_mhz = 50")
expect(rv32_synth_template).to_contain("actual_luts = 0")
expect(rv64_synth_template).to_contain("max_luts = 45000")
expect(rv64_synth_template).to_contain("target_mhz = 50")
expect(bundle_readme_text).to_contain("per-arch boot products manifest: `board_linux_boot_products.sdn`")
expect(bundle_readme_text).to_contain("`riscv_product.byl`")
expect(bundle_readme_text).to_contain("`synth/rv32_synth.sdn`, `synth/rv64_synth.sdn`")
expect(bundle_readme_text).to_contain("Contract files are listed by `contract_file`")
expect(rv32_sidecar).to_contain("\"productLevel\": \"linux-rtl\"")
expect(rv64_sidecar).to_contain("\"configurationProfile\": \"qemu-virt+fpga-board\"")
expect(rv32_sidecar).to_contain("\"rtlBudget\": {\"maxLuts\": 25000, \"targetMhz\": 50}")
expect(rv64_sidecar).to_contain("\"rtlBudget\": {\"maxLuts\": 45000, \"targetMhz\": 50}")
expect(rv32_sidecar).to_contain("\"readiness\": \"contract-not-ready\"")
expect(rv32_sidecar).to_contain("\"formal\": {\"flow\": \"rvfi+sby\", \"gate\": \"placeholder-rejected\", \"status\": \"contract-not-ready\"")
expect(rv32_sidecar).to_contain("\"harness\": \"/tmp/simple_riscv_fpga_system_spec/rv32/rtl/simple_rv32gc_core_formal.vhd\"")
expect(rv32_sidecar).to_contain("\"sby\": \"/tmp/simple_riscv_fpga_system_spec/rv32/rtl/simple_rv32gc_core.sby\"")
expect(rv32_sidecar).to_contain("\"sourceMap\": []")
expect(rv32_sidecar).to_contain("tb_generated_rv32_linux_handoff.vhd")
expect(rv32_sidecar).to_contain("\"runnerSuccessMarkers\": {}")
expect(rv32_core_vhdl).to_contain("rvfi_valid")
expect(rv32_core_vhdl).to_contain("rvfi_mem_wdata")
expect(rv32_core_vhdl).to_contain("GENERATED_RTL_NOT_IMPLEMENTED lane=rv32")
expect(rv32_formal_vhdl).to_contain("entity simple_rv32gc_core_formal is")
expect(rv32_formal_vhdl).to_contain("formal-proof-unavailable")
expect(rv32_sby).to_contain("mode prove")
expect(rv32_sby).to_contain("smtbmc")
expect(rv32_formal_manifest).to_contain("runner = \"sby -f simple_rv32gc_core.sby\"")
expect(rv64_sidecar).to_contain("\"readiness\": \"contract-not-ready\"")
expect(rv64_sidecar).to_contain("\"formal\": {\"flow\": \"rvfi+sby\", \"gate\": \"placeholder-rejected\", \"status\": \"contract-not-ready\"")
expect(rv64_sidecar).to_contain("\"harness\": \"/tmp/simple_riscv_fpga_system_spec/rv64/rtl/simple_rv64gc_core_formal.vhd\"")
expect(rv64_sidecar).to_contain("\"sby\": \"/tmp/simple_riscv_fpga_system_spec/rv64/rtl/simple_rv64gc_core.sby\"")
expect(rv64_sidecar).to_contain("\"sourceMap\": []")
expect(rv64_core_vhdl).to_contain("rvfi_valid")
expect(rv64_core_vhdl).to_contain("rvfi_mem_wdata")
expect(rv64_core_vhdl).to_contain("GENERATED_RTL_NOT_IMPLEMENTED lane=rv64")
expect(rv64_formal_vhdl).to_contain("entity simple_rv64gc_core_formal is")
expect(rv64_formal_vhdl).to_contain("formal-proof-unavailable")
expect(rv64_sby).to_contain("mode prove")
expect(rv64_sby).to_contain("smtbmc")
expect(rv64_formal_manifest).to_contain("runner = \"sby -f simple_rv64gc_core.sby\"")
```

</details>

#### emits MLK-specific bundle metadata for board-level hardware wrappers

- Verify: emits MLK-specific bundle metadata for board-level hardware wrappers
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RFL-001 REQ-RFL-004 REQ-RFL-001..003 REQ-RFL-004..006
step("Verify: emits MLK-specific bundle metadata for board-level hardware wrappers")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: propagates a custom configuration profile into manifest and sidecars
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RFL-001 REQ-RFL-004 REQ-RFL-001..003 REQ-RFL-004..006
step("Verify: propagates a custom configuration profile into manifest and sidecars")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: propagates custom product level, RTL size, and performance budgets into manifest and sidecars
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RFL-001 REQ-RFL-004 REQ-RFL-001..003 REQ-RFL-004..006
step("Verify: propagates custom product level, RTL size, and performance budgets into manifest and sidecars")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `50b8d0d165619e46ef5646356ddeb5b62e3c6c2135dc1deeaec7e8d2ff4002ae`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `50b8d0d165619e46ef5646356ddeb5b62e3c6c2135dc1deeaec7e8d2ff4002ae`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `50b8d0d165619e46ef5646356ddeb5b62e3c6c2135dc1deeaec7e8d2ff4002ae`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/hardware/feature/riscv_fpga_linux_spec.spl
mirror: doc/06_spec/03_system/app/hardware/feature/riscv_fpga_linux_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/hardware/feature/riscv_fpga_linux_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/hardware/feature/riscv_fpga_linux_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/hardware/feature/riscv_fpga_linux_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
