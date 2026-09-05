# riscv_rtl_debuggability_spec

> Purpose: Prove that RISC-V RTL debuggability lint.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# riscv_rtl_debuggability_spec

Purpose: Prove that RISC-V RTL debuggability lint.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/riscv_rtl_debuggability_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that RISC-V RTL debuggability lint.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### RISC-V RTL debuggability lint

#### accepts clean generated RV64 debug sidecars

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts clean generated RV64 debug sidecars
- Verify: accepts clean generated RV64 debug sidecars
   - Expected: run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_clean'") equals `0`
   - Expected: result.is_ok() is true
   - Expected: has_code(results, "RTLDBG001") is false
   - Expected: has_code(results, "RTLDBG002") is false
   - Expected: has_code(results, "RTLDBG003") is false
   - Expected: has_warn_code(results, "RTLDBG102") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts clean generated RV64 debug sidecars")
step("Verify: accepts clean generated RV64 debug sidecars")
# @req: REQ-COMPILER-LINT-001
expect(run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_clean'")).to_equal(0)
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

- emits RTLDBG003 when acceptanceMarkers drift from the generated boot products manifest
- Verify: emits RTLDBG003 when acceptanceMarkers drift from the generated boot products manifest
   - Expected: run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_acceptance_manifest'") equals `0`
   - Expected: result.is_ok() is true
   - Expected: rt_file_write_text(products_manifest_path, broken) is true
   - Expected: has_code(results, "RTLDBG003") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits RTLDBG003 when acceptanceMarkers drift from the generated boot products manifest")
step("Verify: emits RTLDBG003 when acceptanceMarkers drift from the generated boot products manifest")
expect(run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_acceptance_manifest'")).to_equal(0)
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

- emits RTLDBG003 when sidecar and board manifest drift together from the proof-lane contract
- Verify: emits RTLDBG003 when sidecar and board manifest drift together from the proof-lane contract
   - Expected: run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_acceptance_contract'") equals `0`
   - Expected: result.is_ok() is true
   - Expected: rt_file_write_text(sidecar_path, broken) is true
   - Expected: rt_file_write_text(products_manifest_path, broken_products) is true
   - Expected: has_code(results, "RTLDBG003") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits RTLDBG003 when sidecar and board manifest drift together from the proof-lane contract")
step("Verify: emits RTLDBG003 when sidecar and board manifest drift together from the proof-lane contract")
expect(run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_acceptance_contract'")).to_equal(0)
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

- emits RTLDBG001 for malformed sidecars
- Verify: emits RTLDBG001 for malformed sidecars
   - Expected: run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_001'") equals `0`
   - Expected: result.is_ok() is true
   - Expected: rt_file_write_text(sidecar_path, "{}\n") is true
   - Expected: has_code(results, "RTLDBG001") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits RTLDBG001 for malformed sidecars")
step("Verify: emits RTLDBG001 for malformed sidecars")
expect(run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_001'")).to_equal(0)
val result = generate_default_riscv_fpga_rtl_bundle("/tmp/riscv_rtl_debug_lint_001")
expect(result.is_ok()).to_equal(true)
val sidecar_path = "/tmp/riscv_rtl_debug_lint_001/rv64/rtl/simple_rv64gc_core.debug.json"
expect(rt_file_write_text(sidecar_path, "{}\n")).to_equal(true)
val results = lint_core("/tmp/riscv_rtl_debug_lint_001/rv64/rtl/simple_rv64gc_core.vhd")
expect(has_code(results, "RTLDBG001")).to_equal(true)
```

</details>

#### emits RTLDBG002 for source-map mismatches

- emits RTLDBG002 for source-map mismatches
- Verify: emits RTLDBG002 for source-map mismatches
   - Expected: run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_002'") equals `0`
   - Expected: result.is_ok() is true
   - Expected: rt_file_write_text(sidecar_path, broken) is true
   - Expected: has_code(results, "RTLDBG002") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits RTLDBG002 for source-map mismatches")
step("Verify: emits RTLDBG002 for source-map mismatches")
expect(run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_002'")).to_equal(0)
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

- emits RTLDBG003 for manifest/sidecar debug output drift
- Verify: emits RTLDBG003 for manifest/sidecar debug output drift
   - Expected: run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_003'") equals `0`
   - Expected: result.is_ok() is true
   - Expected: rt_file_write_text(manifest_path, broken) is true
   - Expected: has_code(results, "RTLDBG003") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits RTLDBG003 for manifest/sidecar debug output drift")
step("Verify: emits RTLDBG003 for manifest/sidecar debug output drift")
expect(run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_003'")).to_equal(0)
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

- accepts sidecars with non-canonical whitespace
- Verify: accepts sidecars with non-canonical whitespace
   - Expected: run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_ws'") equals `0`
   - Expected: result.is_ok() is true
   - Expected: rt_file_write_text(sidecar_path, spaced) is true
   - Expected: has_code(results, "RTLDBG001") is false
   - Expected: has_code(results, "RTLDBG002") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts sidecars with non-canonical whitespace")
step("Verify: accepts sidecars with non-canonical whitespace")
expect(run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_ws'")).to_equal(0)
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

- emits RTLDBG101 when observability coverage is incomplete
- Verify: emits RTLDBG101 when observability coverage is incomplete
   - Expected: run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_101'") equals `0`
   - Expected: result.is_ok() is true
   - Expected: rt_file_write_text(sidecar_path, broken) is true
   - Expected: has_warn_code(results, "RTLDBG101") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits RTLDBG101 when observability coverage is incomplete")
step("Verify: emits RTLDBG101 when observability coverage is incomplete")
expect(run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_101'")).to_equal(0)
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

- emits RTLDBG102 when proof markers are too thin
- Verify: emits RTLDBG102 when proof markers are too thin
   - Expected: run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_102'") equals `0`
   - Expected: result.is_ok() is true
   - Expected: rt_file_write_text(sidecar_path, broken) is true
   - Expected: has_warn_code(results, "RTLDBG102") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits RTLDBG102 when proof markers are too thin")
step("Verify: emits RTLDBG102 when proof markers are too thin")
expect(run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_102'")).to_equal(0)
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

- emits RTLDBG003 when runnerSuccessMarkers drifts from runner testbench metadata
- Verify: emits RTLDBG003 when runnerSuccessMarkers drifts from runner testbench metadata
   - Expected: run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_runner_success_markers'") equals `0`
   - Expected: result.is_ok() is true
   - Expected: rt_file_write_text(sidecar_path, broken) is true
   - Expected: has_code(results, "RTLDBG003") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits RTLDBG003 when runnerSuccessMarkers drifts from runner testbench metadata")
step("Verify: emits RTLDBG003 when runnerSuccessMarkers drifts from runner testbench metadata")
expect(run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_runner_success_markers'")).to_equal(0)
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

- emits RTLDBG003 when acceptanceMarkers drift from board boot products
- Verify: emits RTLDBG003 when acceptanceMarkers drift from board boot products
   - Expected: run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_acceptance_markers'") equals `0`
   - Expected: result.is_ok() is true
   - Expected: rt_file_write_text(board_products_path, broken) is true
   - Expected: has_code(results, "RTLDBG003") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits RTLDBG003 when acceptanceMarkers drift from board boot products")
step("Verify: emits RTLDBG003 when acceptanceMarkers drift from board boot products")
expect(run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_acceptance_markers'")).to_equal(0)
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

- accepts board boot products manifests with reordered acceptance markers and relaxed spacing
- Verify: accepts board boot products manifests with reordered acceptance markers and relaxed spacing
   - Expected: run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_acceptance_reordered'") equals `0`
   - Expected: result.is_ok() is true
   - Expected: rt_file_write_text(board_products_path, broken) is true
   - Expected: has_code(results, "RTLDBG003") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts board boot products manifests with reordered acceptance markers and relaxed spacing")
step("Verify: accepts board boot products manifests with reordered acceptance markers and relaxed spacing")
expect(run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_acceptance_reordered'")).to_equal(0)
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

- emits RTLDBG003 when a runner file listed in the sidecar is missing
- Verify: emits RTLDBG003 when a runner file listed in the sidecar is missing
   - Expected: run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_runner_missing'") equals `0`
   - Expected: result.is_ok() is true
   - Expected: run_shell("rm -f '/tmp/riscv_rtl_debug_lint_runner_missing/rv64/rtl/tb_generated_rv64_fw_jump.vhd'") equals `0`
   - Expected: has_code(results, "RTLDBG003") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits RTLDBG003 when a runner file listed in the sidecar is missing")
step("Verify: emits RTLDBG003 when a runner file listed in the sidecar is missing")
expect(run_shell("rm -rf '/tmp/riscv_rtl_debug_lint_runner_missing'")).to_equal(0)
val result = generate_default_riscv_fpga_rtl_bundle("/tmp/riscv_rtl_debug_lint_runner_missing")
expect(result.is_ok()).to_equal(true)
expect(run_shell("rm -f '/tmp/riscv_rtl_debug_lint_runner_missing/rv64/rtl/tb_generated_rv64_fw_jump.vhd'")).to_equal(0)
val results = lint_core("/tmp/riscv_rtl_debug_lint_runner_missing/rv64/rtl/simple_rv64gc_core.vhd")
expect(has_code(results, "RTLDBG003")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-LINT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1c0bce608766ce0ea5f1a1ef6cded81273516c8af60708e6243337d7ee51895a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1c0bce608766ce0ea5f1a1ef6cded81273516c8af60708e6243337d7ee51895a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1c0bce608766ce0ea5f1a1ef6cded81273516c8af60708e6243337d7ee51895a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/lint/riscv_rtl_debuggability_spec.spl
mirror: doc/06_spec/01_unit/compiler/lint/riscv_rtl_debuggability_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/lint/riscv_rtl_debuggability_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lint/riscv_rtl_debuggability_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lint/riscv_rtl_debuggability_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/lint/riscv_rtl_debuggability_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts clean generated RV64 debug sidecars' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/riscv_rtl_debuggability_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits RTLDBG003 when acceptanceMarkers drift from the generated boot products manifest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/riscv_rtl_debuggability_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits RTLDBG003 when sidecar and board manifest drift together from the proof-lane contract' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
