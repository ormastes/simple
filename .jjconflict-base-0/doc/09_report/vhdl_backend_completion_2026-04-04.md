# VHDL Backend Completion Report

**Date:** 2026-04-04
**Feature:** VHDL-2008 code generation backend
**Status:** Implemented (bounded scope — analysis/elaboration)

## Summary

The VHDL backend generates synthesizable VHDL-2008 code from Simple MIR, covering entity/architecture/package/process generation. The backend supports GHDL analysis and elaboration validation. Simulation-backed CPU execution and synthesis remain deferred milestones.

## Implementation Stack

| Component | File | Lines | Status |
|-----------|------|-------|--------|
| Backend | `src/compiler/70.backend/backend/vhdl_backend.spl` | 685 | Complete |
| Type Mapper | `src/compiler/70.backend/backend/vhdl_type_mapper.spl` | — | Complete |
| Builder | `src/compiler/70.backend/backend/vhdl_builder.spl` | — | Complete |
| Constraints | `src/compiler/70.backend/backend/vhdl_constraints.spl` | — | Complete |

## Test Coverage

| Test | Type | Tests |
|------|------|-------|
| `test/unit/compiler/backend/vhdl_backend_spec.spl` | Unit | 11 it blocks |
| `test/unit/compiler/backend/vhdl_type_mapper_spec.spl` | Unit | Type mapping |
| `test/unit/compiler/backend/vhdl_builder_spec.spl` | Unit | Builder API |
| `test/unit/compiler/backend/vhdl_constraints_spec.spl` | Unit | Constraints |
| `test/unit/compiler/backend/vhdl_dim_constraints_spec.spl` | Unit | Dimension constraints |
| `test/unit/compiler/backend/vhdl_sim_runner_spec.spl` | Unit | Sim runner |
| `test/unit/compiler/backend/vhdl_testbench_spec.spl` | Unit | Testbench gen |
| `test/integration/compiler/vhdl_backend_e2e_spec.spl` | Integration | E2E path |
| `test/system/vhdl_emulation_spec.spl` | System | GHDL (graceful skip) |
| `test/feature/usage/vhdl_spec.spl` | Feature | Usage patterns |
| `test/feature/usage/vhdl_golden_spec.spl` | Feature | Golden outputs |

## Scope Decisions

| Capability | Status | Notes |
|-----------|--------|-------|
| Entity generation | Implemented | Full port/generic support |
| Architecture generation | Implemented | Signal, process, assignment |
| Package generation | Implemented | Type/constant/function |
| Process compilation | Implemented | Sequential logic |
| Arithmetic operators | Implemented | +, -, *, /, mod |
| Bitwise operators | Implemented | and, or, xor, not |
| Type mapping (int, bool, array) | Implemented | std_logic_vector, integer |
| GHDL analysis (-a) | Implemented | Validated in tests |
| GHDL elaboration (-e) | Implemented | Validated in tests |
| riscv32_sim_vhdl lane | Deferred | Quarantined — simulation milestone |
| GHDL simulation (-r) | Deferred | Follow-on milestone |
| Synthesis | Deferred | Requires vendor toolchain |
| Float types | Deferred | Hard error on unsupported |
| Unit types | Deferred | Hard error on unsupported |
| Pointer types | Deferred | Hard error on unsupported |

## Status Promotion

- **Before:** "Implemented with bounded hardware subset"
- **After:** "Implemented (bounded scope)" — with clear support matrix defining the boundary

## Support Matrix

See `doc/04_architecture/vhdl_support_matrix.md` for detailed capability table.
