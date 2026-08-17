# KV260 tiny-BRAM SoC: firmware runs TWICE per reset on silicon (GHDL runs once)

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

- **Date:** 2026-07-26
- **Severity:** low (cosmetic for current gates — both runs complete and agree; masks nothing today, but breaks any future fw that is not idempotent or that counts on running once)
- **Where:** `examples/09_embedded/fpga_riscv/rtl/soc_top_rv32_tiny_bram.vhd` + `rv32_bram_soc.vhd` reset/obs path on real xck26 silicon (BSCANE2 USER4 obs tunnel readout)

## Symptom
On real KV260 silicon the UART capture buffer holds the firmware transcript
TWICE after a single reset, with `uart_byte_count` exactly 2x the single-run
byte count. Reproduced deterministically on two independent images:

- NVMe self-test fw (29-byte transcript): count = 58 = 2x29, transcript =
  `ALL RV32 NVME FW CHECKS PASS` twice.
  - after initial bitstream configuration:
    `build/fpga/jtag_readout/tiny_bram_transcript_20260726_054618.{log,txt}`
  - after ONE `read_rv32_tiny_bram_obs.shs reset` soft-reset pulse (capture
    verified cleared to count=0 first, `tiny_bram_reset_20260726_054711.log`):
    `build/fpga/jtag_readout/tiny_bram_transcript_20260726_054729.{log,txt}`
- TINY SimpleOS boot (proven "TEST PASSED" lane, 2026-07-26): status readout
  showed count = 0x238 = 568 = 2x284 — same 2x signature
  (`build/fpga/jtag_readout/tiny_bram_status_20260726_045242.log`).

GHDL rehearsal of the EXACT same synth RTL (`tb_rv32_nvme_bram_soc`, same .mem)
runs ONCE: count=29, `build/ghdl/rv32_nvme_bram_soc/sim.log` — so the second
run is silicon-only (STARTUPE3/GSR/BSCANE2 environment), not core/SoC sim logic.

## What is known
- Single capture-clear, double core run: the counter is cleared once (soft-reset
  case proves it: count goes 58 -> 0 -> 58), then the core executes `_start`
  twice. Count is stable afterwards (not a re-execution loop; PC parks in the
  `wfi; j` loop at 0x800002ce/0x800002d2).
- Not the fw: NVMe fw and SimpleOS kernel both show it; GHDL shows neither.
- Harmless for marker-grep verdicts today because both transcripts are complete
  and identical; the `pass_seen`/`fail_seen` matchers are level-latched so they
  are unaffected.

## Suspects (unverified)
- GSR-release vs `rst_cnt` interaction at configuration end (double reset
  release), which would also have to explain the soft-reset reproduction — the
  obs `cmd_toggle`/UPDATE-DR path double-pulsing `obs_cmd_valid` per DR scan
  would explain soft-reset but NOT power-up (and a double 0xF exec would also
  re-clear the counter, which contradicts count=2x).
- `wfi` handling in `rv32_exec_core_axi` interacting with a single spurious
  wake/reset event per reset sequence.

## Next step
Add a run-counter register (increments on each fetch of the reset vector) to
the obs command set and read it on silicon; that separates "core reset twice"
from "PC re-entered _start without reset".
