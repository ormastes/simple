# NAND Emulator (nand_emu) Feature Expert

## Role

Own process knowledge for the K9F8G08X0M-compatible NAND chip emulator:
the per-cell threshold-voltage (Vt) byte model, its command FSM, the
address-shrink profiles, and its role as an alternate NAND backend for the
NVMe firmware's FIL seam.

## Pipeline Links

- Research (source of truth for the device contract):
  [doc/01_research/hardware/nand_emu/nand_emu_fpga_riscv_emulator.md](../../../../doc/01_research/hardware/nand_emu/nand_emu_fpga_riscv_emulator.md)
  — §1 datasheet contract, §3 Vt model + lazy drift, §4 address shrink,
  §7 FSM/physics pseudocode, §8 scenario suite.
- NVMe seam plan:
  [doc/03_plan/hardware/nvme_fw_emulated_nand_plan_tldr.md](../../../../doc/03_plan/hardware/nvme_fw_emulated_nand_plan_tldr.md)

## Code Map

- Module: `src/lib/hardware/nand_emu/` — `nand_types.spl` (all shared `Ne*`
  types, defined ONCE here; interp struct-registry collisions forbid
  redefinition), `geometry.spl`, `vt_array.spl`, `physics.spl`, `cmd_fsm.spl`,
  `status.spl`, `edc.spl`, `badblock.spl`, `fault.spl`, `chip.spl` (NeChip
  pin-level composer), `rtl/pin_frontend.spl` (VHDL-2008 subset spike).
- Specs: `src/lib/hardware/nand_emu/test/*_spec.spl` — `scenario_spec.spl` is
  the user-facing manual (doc §8 subset).
- NVMe adapter: `examples/09_embedded/simpleos_nvme_fw/fw/fil_nand_emu.spl`
  (+ `fil_nand_emu_check.spl`) — opt-in drop-in for the `fil_nand.Nand` seam
  (same API as `fil_nand_device.spl`); NOT the default backend.

## Design Invariants (do not regress)

- One byte per cell: `Vt(code) = (code-128) × 25 mV`; SLC read rule
  `bit = 1 iff code < vref` (erased mean 88, PV 148, default vref 128).
- Lazy drift: retention/disturb applied AT SENSE TIME from page/block meta
  counters; materialized into stored Vt only on program/erase (doc §3.4).
- Per-cell noise derived from `splitmix32(row ^ (col<<3) ^ bit ^ CHIP_SEED)` —
  deterministic, replayable; never store per-cell sigma.
- v1 scope: MODEL timing only (emulated-ns counter, no wall clock), SLC,
  single-plane command set; two-plane/2KB-compat bytes are recognized and
  logged as violations, never faked.
- Unsupported/illegal sequences → NeViolation events, never silent guessing.

## Known Landmines

- JIT/HIR cannot infer struct-typed field `NeChip.geometry` when lowering a
  spec `main` — interpreter fallback is correct and expected; see
  doc/08_tracking/bug/jit_hir_struct_field_type_infer_2026-07-18.md.
- Seed test-runner daemon hangs at init; run specs single-file via
  `timeout 300 bin/simple run <spec>` (guide caveat).

## Related

Layer experts: [backend](../../layer_expert/backend/skill.md) (VHDL subset),
NVMe firmware guide `doc/07_guide/hardware/nvme_firmware/`.
