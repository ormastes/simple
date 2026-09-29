# K26 VexRiscv SoC generation API removed from lib, specs orphaned (2026-09-16)

## Observed
- `test/01_unit/lib/hardware/fpga_k26/k26_soc_top_vexriscv_spec.spl` outcome=ERROR 8/8 failed:
  `semantic: function 'k26_vexriscv_soc_config' not found` (also
  `generate_k26_soc_top_vexriscv`, `K26VexRiscvSocConfig`).
- `test/01_unit/lib/hardware/fpga_linux/synthesis_wrapper_vexriscv_spec.spl`:
  `semantic: function 'synthesis_project_default' not found` (also
  `add_verilog_sources`, `enable_axi_hp_port`).
- No definition of any of these symbols exists anywhere under `src/` (grep clean).

## Impact
Two specs are permanently red; they assert a VexRiscv-SMP K26 generation lane
that was deleted from `src/lib/hardware/fpga_k26/k26_soc_top.spl` and
`src/lib/hardware/fpga_linux/synthesis_wrapper.spl` (which now exposes
`SynthesisProject.create` / `create_synthesis_flow` and an RV64GC VHDL-only TCL).

## Expectation
Either the removed lane is intentionally dead — then delete the specs — or the
API removal was accidental (stale-snapshot clobber) — then restore it. Decide
and reconcile spec vs lib.

## Unblock condition
Owner confirms intent; specs deleted or lib API restored.
