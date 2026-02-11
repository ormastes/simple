# VHDL Backend Plan

**Date**: 2026-02-11  
**Status**: Planned

## Milestones
1. Research checkpoint (this doc + VHDL_SUPPORT_RESEARCH.md) — done.
2. Minimal emitter prototype (single-clock, combinational + sequential, basic types) — 1 week.
3. Type/package support (records, enums, arrays, package emission) — +1 week.
4. Loop/FSM conversion + static checks parity with Verilog backend — +1 week.
5. Tooling & CI smoke (GHDL/Yosys analysis + synth on samples) — +1 week.
6. Documentation, examples, and mixed-language parity review — +3 days.

## Deliverables
- `VhdlBackend` integrated behind `--emit-vhdl`.
- Generated package + entity/architecture files under `build/vhdl/`.
- Static check hooks: bounded loops, width resolution, CDC guardrails, unsynthesizable construct rejection.
- Golden VHDL fixtures and diff tests.
- CI smoke: `ghdl -a -e` and optional `yosys -m ghdl` synth on sample set.
- Docs: research, design, user guide section, limits/waivers notes.

## Work Breakdown
- **Backend scaffolding**: factory wiring, option plumbing, output paths.
- **Emitter core**: entity/architecture templates, signal/reg mapping, sensitivity list generation.
- **Type support**: numeric_std mapping, record/array emit, enum encoding attributes, subtype generation.
- **Control & loops**: for/while with static bounds → unroll or FSM; recursion ban.
- **Checks**: combinational loop detection reuse, width inference enforcement, CDC annotations to sync modules or errors.
- **Packaging**: per-unit package generation, library/use statements, deterministic naming.
- **Tooling**: CLI flags, diagnostic messages consistent with Verilog backend, logging.
- **Testing**: unit tests for mapping, golden emit tests, end-to-end sample synth runs.
- **Docs/examples**: minimal VHDL example, mixed-language note, integration guide updates.

## Dependencies
- Existing MIR → backend abstraction stable.
- Access to GHDL (with LLVM) and ghdl-yosys-plugin in CI container.
- Verilog backend static-check implementations to mirror behavior.

## Risks & Mitigations
- **Toolchain variance**: pin GHDL version in CI; document vendor flow expectations.
- **Delta-cycle/latch surprises**: enforce default assignments and combinational sensitivity lists; add latch detection tests.
- **Schedule creep from FSM conversion**: stage loop support after type/package milestone; keep unroll fallback with caps.

## Exit Criteria (v1)
- All sample designs emit cleanly; `ghdl -a -e` passes.
- Golden diffs stable; no regressions in Verilog backend tests.
- Loop/FSM limits enforced with clear diagnostics.
- Documentation and examples merged.
