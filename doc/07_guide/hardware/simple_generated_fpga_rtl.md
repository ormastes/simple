# Simple-Generated FPGA RTL

This guide shows the current repo-native path for generating FPGA RTL artifacts from Simple source.

## What Gets Generated

The generator emits both:
- generated Simple hardware source (`.spl`)
- generated VHDL artifacts (`.vhd`)

The generated Simple file is the source-of-truth sketch for the emitted VHDL lane. That is the current sample code generation path from Simple code to FPGA-oriented RTL artifacts in this repo.

Authoritative provenance:
- each lane manifest now records `authoritative_rtl_root` as the emitted lane bundle directory, not as the exact authoritative file set
- the precise authoritative generated-core subset is listed by repeated `authoritative_file` entries in the manifest and `provenance.authoritativeFiles` in the debug sidecar
- debug sidecars separately label transitional emitted VHDL wrappers/support packages/testbenches

## List Supported Boards

```bash
bin/simple run src/hardware/fpga_linux/generate_riscv_fpga_bundle.spl -- --list-boards
```

Current output should include:
- `xilinx_generic`
- `mlk_s02_100t`

## Generate a Generic Bundle

```bash
bin/simple run src/hardware/fpga_linux/generate_riscv_fpga_bundle.spl -- /tmp/simple_fpga_bundle
```

Inspect:
- `/tmp/simple_fpga_bundle/riscv_fpga_rtl_manifest.sdn`
- `/tmp/simple_fpga_bundle/vivado_project_plan.tcl`
- `/tmp/simple_fpga_bundle/board_interface_contract.sdn`
- `/tmp/simple_fpga_bundle/README.md`
- `/tmp/simple_fpga_bundle/rv64/rtl/simple_rv64gc_core.spl`
- `/tmp/simple_fpga_bundle/rv64/rtl/simple_rv64gc_core.vhd`

## Generate an MLK-S02-100T Bundle

```bash
bin/simple run src/hardware/fpga_linux/generate_riscv_fpga_bundle.spl -- --board=mlk_s02_100t /tmp/mlk_s02_100t_bundle
```

Inspect:
- `/tmp/mlk_s02_100t_bundle/riscv_fpga_rtl_manifest.sdn`
- `/tmp/mlk_s02_100t_bundle/vivado_project_plan.tcl`
- `/tmp/mlk_s02_100t_bundle/board_interface_contract.sdn`
- `/tmp/mlk_s02_100t_bundle/README.md`
- `/tmp/mlk_s02_100t_bundle/rv64/rtl/simple_rv64gc_core.spl`
- `/tmp/mlk_s02_100t_bundle/rv64/rtl/simple_rv64gc_core.vhd`

Expected manifest differences for `mlk_s02_100t`:
- board id is concrete instead of `xilinx_generic`
- part is `xc7a100t-2ffg484i`
- downstream build directories can stay board-scoped
- Vivado plan is emitted as a board-scoped scaffold even before constraints are verified

Current constraint status for `mlk_s02_100t`:
- the repo includes a board-specific scaffold at `examples/09_embedded/fpga_riscv/constraints/mlk_s02_100t.xdc`
- it is intentionally a commented template, not a verified pin map

Current logical I/O contract status for `mlk_s02_100t`:
- the bundle also emits `board_interface_contract.sdn`
- this records logical names such as `clk25`, `rst_n`, `uart_tx`, `uart_rx`, `led`, and `btn`
- it is the stable non-pin-specific interface layer for future board support
- the bundle also emits `board_linux_boot_products.sdn`, which records the per-arch UART Linux boot markers required on the board flow

## Important Boundary

This generation path proves:
- the Simple hardware source can be materialized
- the VHDL package/core artifacts can be materialized
- the board profile can be selected structurally
- generated RV64 acceptance is stronger than bounded proof-only status: the current repo-native RV64 smoke flow also builds and runs the local generated Linux payload lane after its proof gates

This does not prove:
- constraints are complete
- synthesis passes
- bitstream programming passes
- hardware runtime behavior passes
- the remaining runner/testbench surface is template-free end-to-end; some emitted benches are still transitional template-backed artifacts

Use this as the source generation step before board-specific XDC, Vivado, and runtime validation.
