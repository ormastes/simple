# Riscv Rtl Debuggability Specification

> <details>

<!-- sdn-diagram:id=riscv_rtl_debuggability_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv_rtl_debuggability_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv_rtl_debuggability_spec -> std
riscv_rtl_debuggability_spec -> compiler
riscv_rtl_debuggability_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv_rtl_debuggability_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv Rtl Debuggability Specification

## Scenarios

### RISC-V RTL debuggability lint

#### accepts clean generated RV64 debug sidecars

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shell("rm -rf '/tmp/riscv_rtl_debug_lint_clean'")).to_equal(0)
val result = generate_default_riscv_fpga_rtl_bundle("/tmp/riscv_rtl_debug_lint_clean")
expect(result.is_ok()).to_equal(true)
val core_path = "/tmp/riscv_rtl_debug_lint_clean/rv64/rtl/simple_rv64gc_core.vhd"
val results = lint_core(core_path)
expect(has_code(results, "RTLDBG001")).to_equal(false)
expect(has_code(results, "RTLDBG002")).to_equal(false)
expect(has_code(results, "RTLDBG003")).to_equal(false)
expect(has_warn_code(results, "RTLDBG102")).to_equal(false)
```

</details>

#### emits RTLDBG003 when acceptanceMarkers drift from the generated boot products manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shell("rm -rf '/tmp/riscv_rtl_debug_lint_acceptance_manifest'")).to_equal(0)
val result = generate_default_riscv_fpga_rtl_bundle("/tmp/riscv_rtl_debug_lint_acceptance_manifest")
expect(result.is_ok()).to_equal(true)
val products_manifest_path = "/tmp/riscv_rtl_debug_lint_acceptance_manifest/board_linux_boot_products.sdn"
val products_manifest = read_generated_riscv_fpga_rtl_file(products_manifest_path)
val broken = products_manifest.replace("expected_markers = \"OpenSBI|Linux version|OF: fdt|Freeing unused kernel memory|init started\"", "expected_markers = \"OpenSBI|Linux version|OF: fdt|Freeing unused kernel memory\"")
expect(rt_file_write_text(products_manifest_path, broken)).to_equal(true)
val results = lint_core("/tmp/riscv_rtl_debug_lint_acceptance_manifest/rv64/rtl/simple_rv64gc_core.vhd")
expect(has_code(results, "RTLDBG003")).to_equal(true)
```

</details>

#### emits RTLDBG003 when sidecar and board manifest drift together from the proof-lane contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shell("rm -rf '/tmp/riscv_rtl_debug_lint_acceptance_contract'")).to_equal(0)
val result = generate_default_riscv_fpga_rtl_bundle("/tmp/riscv_rtl_debug_lint_acceptance_contract")
expect(result.is_ok()).to_equal(true)
val sidecar_path = "/tmp/riscv_rtl_debug_lint_acceptance_contract/rv64/rtl/simple_rv64gc_core.debug.json"
val sidecar = read_generated_riscv_fpga_rtl_file(sidecar_path)
val broken = sidecar.replace("\"acceptanceMarkers\": [\"OpenSBI\", \"Linux version\", \"OF: fdt\", \"Freeing unused kernel memory\", \"init started\"]", "\"acceptanceMarkers\": [\"OpenSBI\", \"Linux version\", \"OF: fdt\", \"Freeing unused kernel memory\", \"uart-login-prompt\"]")
expect(rt_file_write_text(sidecar_path, broken)).to_equal(true)
val products_manifest_path = "/tmp/riscv_rtl_debug_lint_acceptance_contract/board_linux_boot_products.sdn"
val products_manifest = read_generated_riscv_fpga_rtl_file(products_manifest_path)
val broken_products = products_manifest.replace("expected_markers = \"OpenSBI|Linux version|OF: fdt|Freeing unused kernel memory|init started\"", "expected_markers = \"OpenSBI|Linux version|OF: fdt|Freeing unused kernel memory|uart-login-prompt\"")
expect(rt_file_write_text(products_manifest_path, broken_products)).to_equal(true)
val results = lint_core("/tmp/riscv_rtl_debug_lint_acceptance_contract/rv64/rtl/simple_rv64gc_core.vhd")
expect(has_code(results, "RTLDBG003")).to_equal(true)
```

</details>

#### emits RTLDBG001 for malformed sidecars

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shell("rm -rf '/tmp/riscv_rtl_debug_lint_001'")).to_equal(0)
val result = generate_default_riscv_fpga_rtl_bundle("/tmp/riscv_rtl_debug_lint_001")
expect(result.is_ok()).to_equal(true)
val sidecar_path = "/tmp/riscv_rtl_debug_lint_001/rv64/rtl/simple_rv64gc_core.debug.json"
expect(rt_file_write_text(sidecar_path, "{}\n")).to_equal(true)
val results = lint_core("/tmp/riscv_rtl_debug_lint_001/rv64/rtl/simple_rv64gc_core.vhd")
expect(has_code(results, "RTLDBG001")).to_equal(true)
```

</details>

#### emits RTLDBG002 for source-map mismatches

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shell("rm -rf '/tmp/riscv_rtl_debug_lint_002'")).to_equal(0)
val result = generate_default_riscv_fpga_rtl_bundle("/tmp/riscv_rtl_debug_lint_002")
expect(result.is_ok()).to_equal(true)
val sidecar_path = "/tmp/riscv_rtl_debug_lint_002/rv64/rtl/simple_rv64gc_core.debug.json"
val sidecar = read_generated_riscv_fpga_rtl_file(sidecar_path)
val broken = sidecar.replace("\"signal\":\"Rv64Instruction.opcode\",\"slice\":\"imem_rdata(6 downto 0)\"", "\"signal\":\"Rv64Instruction.opcode\",\"slice\":\"imem_rdata(5 downto 0)\"")
expect(rt_file_write_text(sidecar_path, broken)).to_equal(true)
val results = lint_core("/tmp/riscv_rtl_debug_lint_002/rv64/rtl/simple_rv64gc_core.vhd")
expect(has_code(results, "RTLDBG002")).to_equal(true)
```

</details>

#### emits RTLDBG003 for manifest/sidecar debug output drift

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shell("rm -rf '/tmp/riscv_rtl_debug_lint_003'")).to_equal(0)
val result = generate_default_riscv_fpga_rtl_bundle("/tmp/riscv_rtl_debug_lint_003")
expect(result.is_ok()).to_equal(true)
val manifest_path = "/tmp/riscv_rtl_debug_lint_003/riscv_fpga_rtl_manifest.sdn"
val manifest = read_generated_riscv_fpga_rtl_file(manifest_path)
val broken = manifest.replace("debug_output = \"debug_pc\"\n", "")
expect(rt_file_write_text(manifest_path, broken)).to_equal(true)
val results = lint_core("/tmp/riscv_rtl_debug_lint_003/rv64/rtl/simple_rv64gc_core.vhd")
expect(has_code(results, "RTLDBG003")).to_equal(true)
```

</details>

#### accepts sidecars with non-canonical whitespace

1. var spaced = sidecar replace
2. spaced = spaced replace
3. spaced = spaced replace
   - Expected: rt_file_write_text(sidecar_path, spaced) is true
   - Expected: has_code(results, "RTLDBG001") is false
   - Expected: has_code(results, "RTLDBG002") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shell("rm -rf '/tmp/riscv_rtl_debug_lint_ws'")).to_equal(0)
val result = generate_default_riscv_fpga_rtl_bundle("/tmp/riscv_rtl_debug_lint_ws")
expect(result.is_ok()).to_equal(true)
val sidecar_path = "/tmp/riscv_rtl_debug_lint_ws/rv64/rtl/simple_rv64gc_core.debug.json"
val sidecar = read_generated_riscv_fpga_rtl_file(sidecar_path)
var spaced = sidecar.replace("\"proofLane\":", "\"proofLane\" : ")
spaced = spaced.replace("\"debugOutputs\":", "\"debugOutputs\"  : ")
spaced = spaced.replace("\"runnerTestbenches\":", "\"runnerTestbenches\" : ")
expect(rt_file_write_text(sidecar_path, spaced)).to_equal(true)
val results = lint_core("/tmp/riscv_rtl_debug_lint_ws/rv64/rtl/simple_rv64gc_core.vhd")
expect(has_code(results, "RTLDBG001")).to_equal(false)
expect(has_code(results, "RTLDBG002")).to_equal(false)
```

</details>

#### emits RTLDBG101 when observability coverage is incomplete

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shell("rm -rf '/tmp/riscv_rtl_debug_lint_101'")).to_equal(0)
val result = generate_default_riscv_fpga_rtl_bundle("/tmp/riscv_rtl_debug_lint_101")
expect(result.is_ok()).to_equal(true)
val sidecar_path = "/tmp/riscv_rtl_debug_lint_101/rv64/rtl/simple_rv64gc_core.debug.json"
val sidecar = read_generated_riscv_fpga_rtl_file(sidecar_path)
val broken = sidecar.replace("\"registerProbes\": true", "\"registerProbes\": false")
expect(rt_file_write_text(sidecar_path, broken)).to_equal(true)
val results = lint_core("/tmp/riscv_rtl_debug_lint_101/rv64/rtl/simple_rv64gc_core.vhd")
expect(has_warn_code(results, "RTLDBG101")).to_equal(true)
```

</details>

#### emits RTLDBG102 when proof markers are too thin

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shell("rm -rf '/tmp/riscv_rtl_debug_lint_102'")).to_equal(0)
val result = generate_default_riscv_fpga_rtl_bundle("/tmp/riscv_rtl_debug_lint_102")
expect(result.is_ok()).to_equal(true)
val sidecar_path = "/tmp/riscv_rtl_debug_lint_102/rv64/rtl/simple_rv64gc_core.debug.json"
val sidecar = read_generated_riscv_fpga_rtl_file(sidecar_path)
val broken = sidecar.replace("\"reportMarkers\": [\"PASS_WORD:\", \"A0_LOW32:\", \"A1_LOW32:\", \"UART_BYTES_LOW32:\", \"PC_LOW32:\", \"DTB_PROBE_SEEN:\", \"TRAP_EDGE_PC_HEX32\", \"HALT_EDGE_PC_HEX32\", \"HEARTBEAT_PC_HEX32\", \"PROGRESS_PC_HEX32\", \"CHECK_PRIV_MODE_OK:\", \"TRAP_CAUSE_WORD:\", \"TRAP_TVAL_WORD:\", \"CAUSE_WORD:\", \"TVAL_WORD:\"]", "\"reportMarkers\": [\"TRAP_EDGE_PC_HEX32\"]")
expect(rt_file_write_text(sidecar_path, broken)).to_equal(true)
val results = lint_core("/tmp/riscv_rtl_debug_lint_102/rv64/rtl/simple_rv64gc_core.vhd")
expect(has_warn_code(results, "RTLDBG102")).to_equal(true)
```

</details>

#### emits RTLDBG003 when runnerSuccessMarkers drifts from runner testbench metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shell("rm -rf '/tmp/riscv_rtl_debug_lint_runner_success_markers'")).to_equal(0)
val result = generate_default_riscv_fpga_rtl_bundle("/tmp/riscv_rtl_debug_lint_runner_success_markers")
expect(result.is_ok()).to_equal(true)
val sidecar_path = "/tmp/riscv_rtl_debug_lint_runner_success_markers/rv64/rtl/simple_rv64gc_core.debug.json"
val sidecar = read_generated_riscv_fpga_rtl_file(sidecar_path)
val broken = sidecar.replace("\"tb_generated_rv64_fw_jump.vhd\":\"GENERATED_RV64_FW_JUMP: PASS\"", "\"tb_generated_rv64_fw_jump.vhd\":\"BROKEN_FW_JUMP_PASS\"")
expect(rt_file_write_text(sidecar_path, broken)).to_equal(true)
val results = lint_core("/tmp/riscv_rtl_debug_lint_runner_success_markers/rv64/rtl/simple_rv64gc_core.vhd")
expect(has_code(results, "RTLDBG003")).to_equal(true)
```

</details>

#### emits RTLDBG003 when acceptanceMarkers drift from board boot products

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shell("rm -rf '/tmp/riscv_rtl_debug_lint_acceptance_markers'")).to_equal(0)
val result = generate_default_riscv_fpga_rtl_bundle("/tmp/riscv_rtl_debug_lint_acceptance_markers")
expect(result.is_ok()).to_equal(true)
val board_products_path = "/tmp/riscv_rtl_debug_lint_acceptance_markers/board_linux_boot_products.sdn"
val board_products = read_generated_riscv_fpga_rtl_file(board_products_path)
val broken = board_products.replace("Linux version|", "")
expect(rt_file_write_text(board_products_path, broken)).to_equal(true)
val results = lint_core("/tmp/riscv_rtl_debug_lint_acceptance_markers/rv64/rtl/simple_rv64gc_core.vhd")
expect(has_code(results, "RTLDBG003")).to_equal(true)
```

</details>

#### accepts board boot products manifests with reordered acceptance markers and relaxed spacing

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shell("rm -rf '/tmp/riscv_rtl_debug_lint_acceptance_reordered'")).to_equal(0)
val result = generate_default_riscv_fpga_rtl_bundle("/tmp/riscv_rtl_debug_lint_acceptance_reordered")
expect(result.is_ok()).to_equal(true)
val board_products_path = "/tmp/riscv_rtl_debug_lint_acceptance_reordered/board_linux_boot_products.sdn"
val board_products = read_generated_riscv_fpga_rtl_file(board_products_path)
val broken = board_products.replace("expected_markers = \"OpenSBI|Linux version|OF: fdt|Freeing unused kernel memory|init started\"", "expected_markers    =    \"init started | Freeing unused kernel memory | OF: fdt | Linux version | OpenSBI\"")
expect(rt_file_write_text(board_products_path, broken)).to_equal(true)
val results = lint_core("/tmp/riscv_rtl_debug_lint_acceptance_reordered/rv64/rtl/simple_rv64gc_core.vhd")
expect(has_code(results, "RTLDBG003")).to_equal(false)
```

</details>

#### emits RTLDBG003 when a runner file listed in the sidecar is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shell("rm -rf '/tmp/riscv_rtl_debug_lint_runner_missing'")).to_equal(0)
val result = generate_default_riscv_fpga_rtl_bundle("/tmp/riscv_rtl_debug_lint_runner_missing")
expect(result.is_ok()).to_equal(true)
expect(shell("rm -f '/tmp/riscv_rtl_debug_lint_runner_missing/rv64/rtl/tb_generated_rv64_fw_jump.vhd'")).to_equal(0)
val results = lint_core("/tmp/riscv_rtl_debug_lint_runner_missing/rv64/rtl/simple_rv64gc_core.vhd")
expect(has_code(results, "RTLDBG003")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/riscv_rtl_debuggability_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RISC-V RTL debuggability lint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
