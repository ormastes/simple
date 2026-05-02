# MLK-S02-100T Assumed Profile

This note records a **provisional, assumption-driven** MLK-S02-100T profile for cases where work must continue before the seller archive arrives.

## Status

- non-authoritative
- intentionally allowed to be wrong
- not acceptable as final board support evidence
- useful only for scaffolding, integration prep, and discussion

## Why This Exists

The repo currently has:

- a real generated Linux bundle flow
- a real wrapper script and boot verifier
- a placeholder official MLK XDC scaffold
- no authoritative vendor archive

This document and its paired XDC let work continue under explicit assumptions without corrupting the default verified-vs-placeholder boundary.

## Assumptions Chosen

These assumptions come from unverified secondary claims rather than from the vendor archive.

- FPGA:
  - tooling target under test: `xc7a100tfgg484-2`
  - assumed pin-map source still came from unverified secondary material
- assumed main clock:
  - pin `W19`
  - frequency `50 MHz`
- assumed reset:
  - pin `V18`
  - active-low
- assumed UART:
  - `uart_rx` on `L19`
  - `uart_tx` on `L20`
- assumed LED0:
  - `M22`

## Known Conflict With Public Vendor Manual

The public MiLianKe hardware manual currently says:

- onboard clock: `25 MHz`
- DDR3: `256MB`
- DDR3 bus width: `16-bit`

That conflicts with the unverified stronger claims that suggested:

- `50 MHz`
- `512MB`
- `32-bit`

For that reason, this profile is deliberately segregated from the default repo MLK path.

## Assumption Validation Lane

The canonical provisional campaign entrypoint is:

```bash
sh scripts/mlk_s02_100t_assumption_validation.shs
```

That runner locks the board to the assumption-only lane for both `rv32` and `rv64`:

- `--allow-assumed-board-top`
- `--allow-unsafe-assumed-bitstream`
- `--vendor-xdc=examples/09_embedded/fpga_riscv/constraints/mlk_s02_100t_assumed_unverified.xdc`

It writes a per-run matrix under `build/fpga/mlk_s02_100t/assumption_validation/` with:

- exact commands
- per-stage logs
- bitstream/program/UART evidence paths
- a provisional assumption ledger that classifies each guessed fact as:
  - confirmed by toolchain only
  - confirmed by programming only
  - confirmed by UART/LED hardware behavior
  - disproven
  - still unknown

## Paired Assumed XDC

Assumption-only XDC:

- [mlk_s02_100t_assumed_unverified.xdc](/home/ormastes/dev/pub/simple/examples/09_embedded/fpga_riscv/constraints/mlk_s02_100t_assumed_unverified.xdc)
- [mlk_s02_100t_assumed_rv32_wrapper.vhd](/home/ormastes/dev/pub/simple/examples/09_embedded/fpga_riscv/rtl/mlk_s02_100t_assumed_rv32_wrapper.vhd)
- [mlk_s02_100t_assumed_rv64_wrapper.vhd](/home/ormastes/dev/pub/simple/examples/09_embedded/fpga_riscv/rtl/mlk_s02_100t_assumed_rv64_wrapper.vhd)

The file intentionally:

- preserves the repo logical clock port name `clk25`
- applies an assumed `50 MHz` timing constraint
- only constrains pins that appeared in the unverified claim set
- leaves the remaining LEDs and buttons explicitly unresolved

## Safe Usage Boundary

This assumed profile may be used to:

- discuss likely board integration steps
- prototype wrapper naming and constraint structure
- compare guessed pinouts against future vendor data
- build assumption-only documentation

It must **not** be used to:

- claim working board support
- claim the pin map is correct
- validate DDR3 wiring
- validate a final synth/program flow
- replace the default MLK placeholder XDC

The assumption-only wrappers deliberately:

- instantiate the generated RV32/RV64 cores
- tie instruction/data memory inputs to zero
- tie interrupts and MMU inputs off
- drive `uart_tx` idle-high
- expose simple debug/trap/halt state on LEDs

That makes them useful only for provisional synth/place/route experiments, not for Linux runtime validation.

## If You Want To Use It Explicitly

Only use it by explicit override, never by changing repo defaults:

```bash
sh scripts/mlk_s02_100t_assumption_validation.shs \
  --arch=rv32
```

For direct wrapper use, keep the same explicit lane:

```bash
sh scripts/mlk_s02_100t_generated_linux.shs \
  --allow-assumed-board-top \
  --allow-unsafe-assumed-bitstream \
  --vendor-xdc=examples/09_embedded/fpga_riscv/constraints/mlk_s02_100t_assumed_unverified.xdc \
  ...
```

## What Still Needs Real Vendor Data

- authoritative `.xdc`
- board-level top HDL or enough HDL/schematic information to build one
- DDR3 topology and MIG settings
- exact clocking truth
- LED/button complete pin map
- boot-flow documentation
- any known-good vendor reference designs
