# Mlk S02 100t Generated Linux Wrapper Specification

> Tests covering MLK-S02-100T generated Linux wrapper scripts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mlk S02 100t Generated Linux Wrapper Specification

## Scenarios

### MLK-S02-100T generated Linux wrapper scripts

#### publishes the board wrapper and boot verifier script names

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- publishes the board wrapper and boot verifier script names


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("publishes the board wrapper and boot verifier script names")
val wrapper = read_text("scripts/mlk_s02_100t_generated_linux.shs")
expect(wrapper).to_contain("scripts/mlk_s02_100t_generated_linux_boot.shs")
expect(wrapper).to_contain("scripts/vivado_mlk_s02_100t_generated_linux.tcl")
expect(wrapper).to_contain("scripts/rtl_riscv32_linux_generated.shs")
expect(wrapper).to_contain("scripts/rtl_riscv64_linux_generated.shs")
```

</details>

#### maps each arch to the expected MLK product id and generated bundle flow

- maps each arch to the expected MLK product id and generated bundle flow


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps each arch to the expected MLK product id and generated bundle flow")
val wrapper = read_text("scripts/mlk_s02_100t_generated_linux.shs")
expect(wrapper).to_contain("echo \"mlk_s02_100t_$1_linux\"")
expect(wrapper).to_contain("--board=mlk_s02_100t")
expect(wrapper).to_contain("src/hardware/fpga_linux/generate_riscv_fpga_bundle.spl")
expect(wrapper).to_contain("ARCH_MODE=\"both\"")
expect(wrapper).to_contain("rv32 rv64")
expect(wrapper).to_contain("BOOT_STAGE_ROOT")
expect(wrapper).to_contain("RV32_BOOT_SOURCE_DIR")
expect(wrapper).to_contain("RV64_BOOT_SOURCE_DIR")
expect(wrapper).to_contain("--prepare-only")
expect(wrapper).to_contain("--allow-assumed-board-top")
expect(wrapper).to_contain("--allow-unsafe-assumed-bitstream")
expect(wrapper).to_contain("stage_boot_artifacts \"$arch\"")
expect(wrapper).to_contain("boot_source_env_var_name()")
expect(wrapper).to_contain("boot_source_dir_for()")
expect(wrapper).to_contain("default_boot_source_relpaths()")
expect(wrapper).to_contain("copy_boot_artifact_from_source_dir()")
expect(wrapper).to_contain("build/third_party/rtl/linux-on-litex-vexriscv/images")
expect(wrapper).to_contain("MLK_")
expect(wrapper).to_contain("_FW_JUMP")
expect(wrapper).to_contain("_IMAGE")
expect(wrapper).to_contain("_DTB")
expect(wrapper).to_contain("_INITRAMFS")
expect(wrapper).to_contain("MLK_BOOT_SOURCE_RV64_DIR")
```

</details>

#### hands synthesis to the MLK Vivado TCL with board-specific arguments

- hands synthesis to the MLK Vivado TCL with board-specific arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hands synthesis to the MLK Vivado TCL with board-specific arguments")
val wrapper = read_text("scripts/mlk_s02_100t_generated_linux.shs")
val vivado_tcl = read_text("scripts/vivado_mlk_s02_100t_generated_linux.tcl")
expect(wrapper).to_contain("vivado -mode batch")
expect(wrapper).to_contain("assert_ready_xdc \"$xdc_path\"")
expect(wrapper).to_contain("PRODUCT_ROOT=\"${MLK_PRODUCT_ROOT:-$BUNDLE_ROOT/products}\"")
expect(wrapper).to_contain("assert_board_topology_ready")
expect(wrapper).to_contain("WARN: using assumption-only MLK board top and XDC for provisional synth")
expect(wrapper).to_contain("MLK_VIVADO_TOP_KIND=assumed_wrapper vivado -mode batch")
expect(wrapper).to_contain("MLK_ALLOW_UNSAFE_BITSTREAM=1")
expect(wrapper).to_contain("FAIL: MLK-S02-100T board wrapper is still a scaffold")
expect(wrapper).to_contain("A real vendor XDC is not sufficient yet because Vivado still targets the raw generated core top.")
expect(wrapper).to_contain("FAIL: XDC is still a placeholder scaffold")
expect(wrapper).to_contain("Provide a verified vendor/user constraint file via --vendor-xdc or MLK_VENDOR_XDC before synth.")
expect(wrapper).to_contain("-source \"$REPO_ROOT/scripts/vivado_mlk_s02_100t_generated_linux.tcl\"")
expect(wrapper).to_contain("-tclargs \"$product_id\" \"$arch\" \"$BUNDLE_ROOT\" \"$product_dir\" \"$xdc_path\"")
expect(wrapper).to_contain("assert_boot_delivery_ready \"$arch\"")
expect(wrapper).to_contain("if [ \"$SKIP_UART\" -ne 1 ] || [ \"$PREPARE_ONLY\" -eq 1 ]; then")
expect(wrapper).to_contain("if [ \"$SKIP_SYNTH\" -ne 1 ]; then")
expect(wrapper).to_contain("boot delivery command not configured; pass --boot-delivery-cmd or set MLK_BOOT_DELIVERY_CMD")
expect(vivado_tcl).to_contain("create_project -force $product_id $project_dir -part xc7a100tfgg484-2")
expect(vivado_tcl).to_contain("MLK_VIVADO_TOP_KIND")
expect(vivado_tcl).to_contain("MLK_ALLOW_UNSAFE_BITSTREAM")
expect(vivado_tcl).to_contain("assumed_wrapper")
expect(vivado_tcl).to_contain("mlk_s02_100t_assumed_rv32_wrapper")
expect(vivado_tcl).to_contain("mlk_s02_100t_assumed_rv64_wrapper")
expect(vivado_tcl).to_contain("downgrading UCIO-1 and NSTD-1 for assumption-only bitstream generation")
expect(vivado_tcl).to_contain("set rtl_dir [file join $bundle_root \"rv32\" \"rtl\"]")
expect(vivado_tcl).to_contain("set rtl_dir [file join $bundle_root \"rv64\" \"rtl\"]")
```

</details>

#### can source default RV32 boot payload filenames from a repo-local source directory

- can source default RV32 boot payload filenames from a repo-local source directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can source default RV32 boot payload filenames from a repo-local source directory")
val wrapper = read_text("scripts/mlk_s02_100t_generated_linux.shs")
expect(wrapper).to_contain("opensbi/fw_jump.bin fw_jump.bin opensbi.bin")
expect(wrapper).to_contain("echo \"$product_id.dtb $arch.dtb\"")
expect(wrapper).to_contain("echo \"$product_id.cpio rootfs.cpio\"")
expect(wrapper).to_contain("Hint: the repo-local RV32 source cache is populated by scripts/rtl_riscv32_linux_litex.shs.")
expect(wrapper).to_contain("Hint: there is no repo-local RV64 split-boot default; set MLK_BOOT_SOURCE_RV64_DIR or MLK_RV64_{FW_JUMP,IMAGE,DTB,INITRAMFS}.")
```

</details>

#### uses the UART verification helper with deterministic Linux boot markers

- uses the UART verification helper with deterministic Linux boot markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the UART verification helper with deterministic Linux boot markers")
val wrapper = read_text("scripts/mlk_s02_100t_generated_linux.shs")
val boot = read_text("scripts/mlk_s02_100t_generated_linux_boot.shs")
expect(wrapper).to_contain("sh \"$REPO_ROOT/scripts/mlk_s02_100t_generated_linux_boot.shs\"")
expect(wrapper).to_contain("BOOT_PRODUCTS_MANIFEST=\"$(boot_products_manifest_path)\"")
expect(wrapper).to_contain("--product-id=\"$product_id\"")
expect(wrapper).to_contain("--boot-products-manifest=\"$BOOT_PRODUCTS_MANIFEST\"")
expect(wrapper).to_contain("\"--boot-loader-cmd=$BOOT_DELIVERY_CMD\"")
expect(boot).to_contain("markers_from_manifest()")
expect(boot).to_contain("expected_markers = \"")
expect(boot).to_contain("missing UART markers; pass --markers or both --boot-products-manifest and --product-id")
expect(boot).to_contain("FAIL: UART markers missing")
expect(boot).to_contain("PASS: UART markers found for $COLD_BOOTS cold boot(s)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/hardware/fpga_linux/mlk_s02_100t_generated_linux_wrapper_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MLK-S02-100T generated Linux wrapper scripts.
- MLK-S02-100T generated Linux wrapper scripts

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3f67a6ec8731d64e141d376967f6e4f53e390495fc3f45439f5b1c936e9f7c5d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3f67a6ec8731d64e141d376967f6e4f53e390495fc3f45439f5b1c936e9f7c5d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3f67a6ec8731d64e141d376967f6e4f53e390495fc3f45439f5b1c936e9f7c5d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/unit/hardware/fpga_linux/mlk_s02_100t_generated_linux_wrapper_spec.spl
mirror: doc/06_spec/unit/hardware/fpga_linux/mlk_s02_100t_generated_linux_wrapper_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/hardware/fpga_linux/mlk_s02_100t_generated_linux_wrapper_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/hardware/fpga_linux/mlk_s02_100t_generated_linux_wrapper_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/hardware/fpga_linux/mlk_s02_100t_generated_linux_wrapper_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes the board wrapper and boot verifier script names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/fpga_linux/mlk_s02_100t_generated_linux_wrapper_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps each arch to the expected MLK product id and generated bundle flow' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/fpga_linux/mlk_s02_100t_generated_linux_wrapper_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hands synthesis to the MLK Vivado TCL with board-specific arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/fpga_linux/mlk_s02_100t_generated_linux_wrapper_spec.spl:85:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can source default RV32 boot payload filenames from a repo-local source directory' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
