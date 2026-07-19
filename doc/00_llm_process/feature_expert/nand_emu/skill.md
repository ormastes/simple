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

## Recovery / prevention lane (2026-07-19)

- Taxonomy of NAND SSD recovery+prevention algorithms:
  `doc/01_research/hardware/nand_recovery/nand_ssd_recovery_prevention_taxonomy.md`
- Local gap analysis (what fw has / lacks, with file:line):
  `doc/01_research/hardware/nand_recovery/nand_recovery_gap_analysis_local.md`
  — headline: vref actuator wired end-to-end but no policy calls it;
  scrub_once / wear_level_once / rain_seal / alloc_spare implemented-but-UNWIRED.
- Architecture (THE LAW: shared logic layer-neutral, placeable on FTL or FIL
  unless it needs L2P/hotness/GC state): `rel_*` module family below `fil`
  (depends only on nvme_types), pure verdict-returning policies + thin
  RelFilMount/RelFtlMount adapters:
  `doc/04_architecture/hardware/nand_recovery/reliability_engine_architecture.md`
- Detail design (v1 SLC-validatable set: ladder, ROR-lite, FCR/DEAR-lite,
  STRAW-lite, SREA-lite, wiring pass):
  `doc/05_design/hardware/nand_recovery/recovery_algorithms_design.md`
- Prerequisite seams before implementing: `FilRead.corrected`,
  `fil.read_at_vref`, NandEmu wrapper re-export of vt_histogram/read_margin.

## Implementation status (2026-07-19: v1 engine LIVE)

- All lanes landed green: `fw/nd_types.spl` (typed NAND dimensions — NdChannel/
  NdWay/NdBank/NdPlane/NdBlock/NdWordline/NdPage value types + NdAddr; only
  channel/block/page are live in address math, others typed-but-decorative per
  `doc/01_research/hardware/nand_recovery/typed_nand_addressing_local.md`),
  `rel_types`, `rel_health`, `rel_vref`, `rel_disturb`, `rel_wear`,
  `rel_refresh`, `rel_ladder` + per-module `*_check.spl` (absolute oracles).
- L8 wiring: ladder mounts in `Fil.read_with_ladder` (production reads recover
  drifted pages: proven depth-2 recovery at cal −16 via `ftl.read`);
  `rel_tick_select` enforces ONE reclaim-class step/tick (GC>refresh>scrub>WL)
  in `nvme_controller.io_process` + `firmware.service_tick`; erase-reset trio +
  retire→`alloc_spare` wired. Gaps A2/A7 of the gap analysis closed;
  `rel_wiring_check.spl` is the integration oracle set.
- rv32 port: deliberately deferred with trigger + port shape in
  `doc/03_plan/hardware/nvme_fw_rel_rv32_port_plan.md` (trigger — rel_* having
  production callers — is now TRUE, so the port is a live follow-up).
- Emulator address math consolidated onto geometry.spl canon (ne_block_of/
  ne_page_in_block/ne_block_first_row); chip.spl `self.` info-lint is a parser
  FALSE POSITIVE (self.field is the body convention — do not "fix" it).

## Related

Layer experts: [backend](../../layer_expert/backend/skill.md) (VHDL subset),
NVMe firmware guide `doc/07_guide/hardware/nvme_firmware/`.
