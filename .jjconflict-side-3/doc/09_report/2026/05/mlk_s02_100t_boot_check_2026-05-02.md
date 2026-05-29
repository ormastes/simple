# MLK-S02-100T Boot Check — 2026-05-02

**Board:** MiLianKe `MLK-S02-100T`  
**Lane:** assumption-only `rv32`  
**Status:** no Linux boot success; programming proof only

## Replan

The current repo state already contains:

- an assumption-only `rv32` bitstream at
  `build/fpga/mlk_s02_100t/generated_linux_bundle/products/mlk_s02_100t_rv32_linux/bitstream/mlk_s02_100t_rv32_linux.bit`
- a generated Linux wrapper and assumption-validation runner
- staged `rv64` boot payloads
- no real MLK board wrapper with memory wiring

That means the only honest near-term boot check is:

1. program the existing `rv32` assumption-only bitstream
2. observe UART
3. classify whether any Linux proof is possible on the current wrapper
4. fix any repo-side misreporting

## What Was Run

Unit verification for the runner:

- `bin/simple test test/unit/hardware/fpga_linux/mlk_s02_100t_assumption_validation_spec.spl`

Direct hardware proof:

- `openFPGALoader build/fpga/mlk_s02_100t/generated_linux_bundle/products/mlk_s02_100t_rv32_linux/bitstream/mlk_s02_100t_rv32_linux.bit`
- passive UART capture on `/dev/ttyUSB0` at `115200 8N1`

Fixed runner replay:

- `sh scripts/mlk_s02_100t_assumption_validation.shs --arch=rv32 --run-id=manual_rv32_bootcheck_20260502T000000Z --skip-ghdl --skip-synth`

Generated artifact root:

- `build/fpga/mlk_s02_100t/assumption_validation/manual_rv32_bootcheck_20260502T000000Z/`

## Observed Result

- JTAG programming succeeded.
- UART passive capture remained empty.
- No `OpenSBI`, `Linux version`, `OF: fdt`, `Freeing unused kernel memory`, or
  `init started` markers were observed.

Fresh generated summary:

- [rv32 summary](/home/ormastes/dev/pub/simple/build/fpga/mlk_s02_100t/assumption_validation/manual_rv32_bootcheck_20260502T000000Z/rv32/summary.md)

Key evidence:

- [program.log](/home/ormastes/dev/pub/simple/build/fpga/mlk_s02_100t/assumption_validation/manual_rv32_bootcheck_20260502T000000Z/rv32/program.log)
- [uart_observation.log](/home/ormastes/dev/pub/simple/build/fpga/mlk_s02_100t/assumption_validation/manual_rv32_bootcheck_20260502T000000Z/rv32/uart_observation.log)
- [linux_launch.log](/home/ormastes/dev/pub/simple/build/fpga/mlk_s02_100t/assumption_validation/manual_rv32_bootcheck_20260502T000000Z/rv32/linux_launch.log)

## Repo Fix Applied

The assumption-validation runner had a misclassification bug:

- any non-empty `linux_launch.log` could be treated as UART/LED success evidence
  even when the log only contained a blocked/error note

Fixed in:

- [scripts/mlk_s02_100t_assumption_validation.shs](/home/ormastes/dev/pub/simple/scripts/mlk_s02_100t_assumption_validation.shs)

The runner now:

- treats Linux proof as success only when `linux_status=pass`
- blocks Linux launch explicitly on the assumption-only wrappers
- records the real reason:
  - memory is tied off
  - `uart_tx` is driven idle-high

Coverage updated in:

- [test/unit/hardware/fpga_linux/mlk_s02_100t_assumption_validation_spec.spl](/home/ormastes/dev/pub/simple/test/unit/hardware/fpga_linux/mlk_s02_100t_assumption_validation_spec.spl)

## Conclusion

Boot check result: **not successful**

What is proven now:

- attached FPGA is programmable from this host
- the existing assumption-only `rv32` bitstream loads successfully

What is not proven:

- UART pin correctness
- memory wiring correctness
- Linux boot on hardware

What blocks real Linux boot on the current repo lane:

- the assumption-only wrappers intentionally tie memory inputs to zero
- the wrappers force `uart_tx <= '1'`
- therefore Linux boot proof is impossible on this wrapper family even with
  valid staged boot artifacts

The next real boot step is not another assumption-only UART retry. It is a
real board-level top with memory/boot-path wiring or authoritative vendor files
that allow one to be built.
