# VHDL Backend Plan

**Date**: 2026-02-11
**Status**: In progress (M1 scaffolding complete)

## Milestones

| # | Milestone | Duration | Dependencies | Key Deliverables |
|---|-----------|----------|-------------|-----------------|
| 1 | Backend scaffolding (enums, factory, CLI) | 1 week | -- | `src/compiler_core/backend_types.spl`, `src/compiler/backend/backend_types.spl`, `backend_helpers.spl`, `backend_factory.spl` |
| 2 | Type mapping + basic entity emission | 1 week | M1 | `vhdl_type_mapper.spl`, `vhdl/vhdl_builder.spl`, `vhdl_backend.spl` |
| 3 | Process model + signal assignment | 1 week | M2 | `VhdlProcess` MIR lowering, combinational + clocked process emission |
| 4 | Width/loop verification (DimSolver) | 1 week | M3 | `dim_constraints_types.spl` (WidthMatch, WidthSafe, BoundedLoop, ValidRange), `dim_constraints.spl` solving logic |
| 5 | Structural verification (CDC, latch, comb loop) | 1 week | M3 (parallel with M4) | `vhdl_constraints.spl` (VhdlConstraintChecker), E07xx error codes |
| 6 | CI integration (GHDL/Yosys SFFI, smoke tests) | 1 week | M4 + M5 | `vhdl_ffi.spl`, golden file tests, `ghdl -a -e` CI smoke |
| 7 | Documentation + examples | 3 days | M6 | Updated research/design/plan docs, user guide section, examples |

## File Location Deliverables

### M1: Backend Scaffolding (DONE)
- `src/compiler_core/backend_types.spl` — `Vhdl` in `CoreBackendKind`, `BACKEND_VHDL = 7`
- `src/compiler/backend/backend_types.spl` — `Vhdl` in `BackendKind`, `is_vhdl_backend()`
- `src/compiler/backend/backend_helpers.spl` — `"vhdl"` in `backend_for_name()`, `available_backends()`
- `src/compiler/backend/backend_factory.spl` — `Vhdl` case in `create_specific()`, `get_description()`

### M2: Type Mapping + Entity Emission
- `src/compiler/backend/vhdl_type_mapper.spl` — VhdlTypeMapper (signed/unsigned/bit/record/enum)
- `src/compiler/backend/vhdl/vhdl_builder.spl` — VhdlBuilder (entity/architecture/package generation)
- `src/compiler/backend/vhdl/mod.spl` — Module re-export
- `src/compiler/backend/vhdl_backend.spl` — VhdlBackend orchestrator

### M3: Process Model
- `src/compiler/mir_data.spl` — VhdlProcess, VhdlSignalAssign, VhdlVarAssign, VhdlPortMap, VhdlResize, VhdlSlice, VhdlConcat MIR instructions
- `src/compiler/mir_data.spl` — VhdlProcessKind, VhdlClockDomain, VhdlClockEdge, VhdlSignalKind, VhdlPortDirection, VhdlSignalResolution, VhdlNumericKind support types

### M4: Width/Loop Verification
- `src/compiler/dim_constraints_types.spl` — WidthMatch, WidthSafe, BoundedLoop, ValidRange constraint variants; WidthMismatch, WidthOverflow, UnboundedLoop, InvalidRange error kinds
- `src/compiler/dim_constraints.spl` — Solving logic for new variants, classify_constraint cases

### M5: Structural Verification
- `src/compiler/vhdl_constraints.spl` — VhdlConstraint enum, VhdlConstraintChecker class, VhdlConstraintError

### M6: CI Integration
- `src/app/io/vhdl_ffi.spl` — GHDL/Yosys SFFI wrappers

### M7: Documentation
- `doc/research/VHDL_SUPPORT_RESEARCH.md` — Constraint system research, CDC/latch/comb loop sections
- `doc/design/VHDL_BACKEND_DESIGN.md` — Full restructure matching GPU design pattern
- `doc/plan/VHDL_BACKEND_PLAN.md` — This file, updated milestones

## Work Breakdown

- **Backend scaffolding**: factory wiring, option plumbing, output paths
- **Emitter core**: entity/architecture templates, signal/reg mapping, sensitivity list generation
- **Type support**: numeric_std mapping, record/array emit, enum encoding, subtype generation
- **Process model**: combinational (sensitivity lists, default assignments), clocked (rising_edge/falling_edge), async reset
- **VHDL MIR instructions**: VhdlProcess, VhdlSignalAssign, VhdlPortMap, VhdlResize, VhdlSlice, VhdlConcat
- **Width verification**: DimSolver integration for WidthMatch, WidthSafe, BoundedLoop, ValidRange
- **Structural verification**: CDC graph coloring, latch branch coverage, Tarjan SCC for comb loops
- **Control & loops**: for/while with static bounds, recursion ban, FSM conversion
- **Packaging**: per-unit package generation, library/use statements, deterministic naming
- **Tooling**: CLI `--backend=vhdl`, diagnostic messages (E07xx), logging
- **SFFI**: GHDL analysis/elaboration/simulation/synthesis wrappers, Yosys integration
- **Testing**: unit tests for mapping, golden emit tests, end-to-end GHDL smoke runs
- **Docs/examples**: minimal VHDL example, integration guide updates

## Dependencies

- Existing MIR -> backend abstraction stable
- `DimSolver`/`DimConstraint` infrastructure in `src/compiler/dim_constraints*.spl`
- Access to GHDL (with LLVM) and ghdl-yosys-plugin in CI container
- GPU backend design pattern (`doc/design/gpu_backend_design.md`) as reference

## Verification Constraint Test Criteria

| Constraint | Test | Expected |
|-----------|------|----------|
| Width mismatch | Assign 8-bit to 16-bit signal | E0700 error |
| Width overflow | Multiply two 32-bit signals into 32-bit result | E0701 error |
| CDC violation | Cross-domain signal without synchronizer | E0710 error |
| Incomplete sensitivity | Process reads signal not in sensitivity list | E0720 error |
| Combinational loop | Signal depends on itself combinationally | E0721 error |
| Latch inference | Signal not assigned in else branch | E0722 error |
| Unbounded loop | Loop with non-static bound | E0730 error |
| Multiple drivers | Two processes drive same unresolved signal | E0740 error |

## Risks & Mitigations

- **Toolchain variance**: pin GHDL version in CI; document vendor flow expectations
- **Delta-cycle/latch surprises**: enforce default assignments and combinational sensitivity lists; add latch detection tests
- **Schedule creep from FSM conversion**: stage loop support after type/package milestone; keep unroll fallback with caps
- **DimSolver integration**: new constraint variants are additive; existing tests remain unaffected

## Exit Criteria (v1)

- All sample designs emit cleanly; `ghdl -a -e` passes
- All compile-time constraints pass on golden examples
- Golden diffs stable; no regressions in other backend tests
- Loop/FSM limits enforced with clear E07xx diagnostics
- VhdlConstraintChecker catches all 8 constraint types listed above
- Documentation and examples merged
