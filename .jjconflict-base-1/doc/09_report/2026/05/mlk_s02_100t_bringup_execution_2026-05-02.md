# MLK-S02-100T Bring-Up Execution Report

**Date:** 2026-05-02
**Board:** MiLianKe `MLK-S02-100T`
**Status:** Partial execution complete, wrapper flow hardened; blocked on vendor bundle and real board topology

## What Was Verified

### Toolchain

- Vivado setup script exists:
  - `/home/ormastes/Xilinx/2025.2/Vivado/settings64.sh`
- Vivado reports:
  - `vivado v2025.2 (64-bit)`
- `openFPGALoader` is installed:
  - `/usr/bin/openFPGALoader`

### Board Connectivity

- USB devices confirm the expected board-side adapters are present:
  - `QinHeng Electronics CH340 serial converter`
  - `Future Technology Devices International, Ltd FT2232C/D/H Dual UART/FIFO IC`
- `/dev/ttyUSB0` exists and matches the intended Linux/U-Boot console lane.
- `/dev/ttyUSB1` and `/dev/ttyUSB2` exist and match the FT2232 interfaces.
- `openFPGALoader --scan-usb` identifies:
  - `MiLianKe.JTAG1U1`
- `openFPGALoader --detect` identifies the FPGA:
  - manufacturer: `xilinx`
  - family: `artix a7 100t`
  - model: `xc7a100`

### Repo-Side Linux Behavioral Gates

- `sh scripts/rtl_riscv64_linux_generated.shs`
  - `PASS: generated_rv64_linux repo-native generated Linux acceptance lane passed`
- `sh scripts/rtl_riscv32_linux_generated.shs`
  - `PASS: generated_rv32_linux repo-native generated Linux acceptance lane passed`

### Generated Bundle

- Generated successfully:
  - `build/fpga/mlk_s02_100t/generated_linux_bundle`
- Manifest present:
  - `build/fpga/mlk_s02_100t/generated_linux_bundle/board_linux_boot_products.sdn`
- Expected Linux UART markers recorded for both `rv32` and `rv64`:
  - `OpenSBI`
  - `Linux version`
  - `OF: fdt`
  - `Freeing unused kernel memory`
  - `init started`

### Wrapper Hardening

- `scripts/mlk_s02_100t_generated_linux.shs --arch=rv64 --skip-ghdl --skip-synth --skip-program --skip-uart`
  now exits successfully instead of failing on unconditional boot staging.
- `scripts/mlk_s02_100t_generated_linux.shs --arch=rv64 --prepare-only --skip-ghdl`
  now supports deterministic boot-artifact preparation when inputs are supplied through:
  - `MLK_RV64_FW_JUMP`
  - `MLK_RV64_IMAGE`
  - `MLK_RV64_DTB`
  - `MLK_RV64_INITRAMFS`
  - and corresponding `RV32` variants
- Wrapper unit coverage passes:
  - `bin/simple test test/unit/hardware/fpga_linux/mlk_s02_100t_generated_linux_wrapper_spec.spl`

### Provisional Assumption-Only Synthesis

The repo now contains an assumption-only MLK lane:

- `--allow-assumed-board-top`
- assumption-only XDC:
  - `examples/09_embedded/fpga_riscv/constraints/mlk_s02_100t_assumed_unverified.xdc`
- assumption-only wrappers:
  - `mlk_s02_100t_assumed_rv32_wrapper.vhd`
  - `mlk_s02_100t_assumed_rv64_wrapper.vhd`

Verified on `2026-05-02`:

- corrected Vivado part string:
  - `xc7a100tfgg484-2`
- provisional RV32 assumption-only lane:
  - synthesis succeeded
  - placement succeeded
  - routing succeeded

Without any unsafe override, bitstream generation stops only on the expected unresolved-assumption I/O checks:

- `NSTD-1`
- `UCIO-1`

Affected unresolved ports in the assumption-only lane:

- `btn[1]`
- `btn[0]`
- `led[7:1]`

An additional explicit opt-in now exists for experimentation only:

- `--allow-unsafe-assumed-bitstream`

That path is intentionally segregated from normal MLK support because it downgrades final DRC checks for unconstrained assumption-only I/O.

## Current Blockers

### 1. Vendor XDC Not Present

No vendor bundle or authoritative `.xdc` is present under:
- `third_party/board_vendor/mlk_s02_100t/`

Current repo state still points to a placeholder/scaffold constraint path unless a real vendor XDC is supplied via:
- `--vendor-xdc`
- `MLK_VENDOR_XDC`

Without that file, the board wrapper preflight cannot be satisfied for synth/program execution.

### 2. Real Board-Level Topology Is Not Ready For Synthesis

The current Vivado flow still targets the raw generated core, not a real MLK board wrapper.

Current repo evidence:
- `scripts/vivado_mlk_s02_100t_generated_linux.tcl` sets the top to:
  - `simple_rv32gc_core`
  - `simple_rv64gc_core`
- `examples/09_embedded/fpga_riscv/rtl/mlk_s02_100t_wrapper_stub.vhd` is still an unwired scaffold.

The wrapper now fails explicitly before synth if that scaffold is still in place.

This means a real vendor XDC alone is still insufficient; a board-level top matching:
- `clk25`
- `rst_n`
- `uart_tx`
- `uart_rx`
- `led`
- `btn`

must be wired first.

### 3. Board Boot Payload Staging Is Empty Unless Supplied

The wrapper expects pre-staged per-arch boot files under:
- `build/fpga/mlk_s02_100t/boot_sources/rv64/`
- `build/fpga/mlk_s02_100t/boot_sources/rv32/`

Required files are absent:
- `opensbi/fw_jump.bin`
- `Image`
- `mlk_s02_100t_<arch>_linux.dtb`
- `mlk_s02_100t_<arch>_linux.cpio`

The generated FPGA bundle emits the board/product manifest, but it does not populate these boot payload directories by itself.

The wrapper now also accepts direct per-arch env overrides for these artifacts, but no real payload set was available locally in this session.

### 4. UART Console Did Not Emit Output In Passive Probe

Passive reads and newline nudges on `/dev/ttyUSB0` at `115200 8N1` produced no observable output during this session.

This means the serial boot delivery flow could not be derived from a live U-Boot prompt here, and no vendor-documented command sequence was available locally to validate against.

## Outcome

The MLK bring-up plan is executable up to the hardware prerequisites boundary:

- host toolchain is ready
- board is physically visible over JTAG
- generated Linux RTL acceptance passes for both arches
- board bundle generation and boot-marker contracts are present
- wrapper prep mode and skip-mode behavior are now deterministic and test-covered

The following plan steps remain blocked:

- acquire the authoritative MiLianKe vendor bundle
- supply the real `MLK-S02-100T` XDC
- replace the scaffold board wrapper with a real board-level top
- materialize staged boot payloads for `rv64` and `rv32`
- define and validate the exact U-Boot serial load command sequence
- synthesize, program, and verify Linux boot on hardware

## Next Required Inputs

To continue, provide:

1. The vendor bundle unpacked under:
   - `third_party/board_vendor/mlk_s02_100t/unpacked/`
2. The authoritative XDC path from that bundle.
3. The vendor board boot-flow notes, or an already known working U-Boot serial-load sequence.
4. The staged boot payloads for:
   - `rv64`
   - `rv32`
