# SStack State: vhdl-riscv-hardware-spawn

## Task
- **Type:** feature
- **Goal:** Implement typed return labels, hardware call lowering, and bit-width semantics for hardware spawn from Simple to VHDL/RTL
- **Plan:** `doc/03_plan/agent_tasks/pure_simple_vhdl_riscv_gap_spawn_plan.md`

## Acceptance Criteria
1. HardwareAttr preserves `@hardware`, `@generic`, `@clocked` annotations through AST/HIR/MIR with labeled return fields
2. ReturnLabel carries field name, type, bit-width, direction; rejects duplicates before backend emission
3. HardwareCallInstance lowers direct `@hardware` calls into VHDL entity instances with deterministic naming and named port maps
4. CallLowerResult rejects indirect calls, dynamic tuple access, and recursion with diagnostic messages
5. BitWidth supports u1..u64 fixed-width types with VHDL type emission (std_logic, signed, unsigned)
6. BitSlice supports typed slicing, concatenation, sign/zero extension, truncation with width-mismatch diagnostics
7. HardwareSpawnLower orchestrates the full lowering pipeline: validate attrs -> resolve labels -> lower calls -> emit VHDL signals

## Phase Progress
- [x] Phase 1 (dev): ACs defined
- [x] Phase 2 (research): Found existing modules in src/compiler/70.backend/backend/vhdl/
- [x] Phase 3 (arch): Designed typed return labels and hardware call lowering
- [x] Phase 5 (implement): Created modules
- [x] Phase 7 (verify): Syntax check (passed, fixed string repeat pattern)
- [x] Phase 8 (ship): Commit

## Key Files
- `src/compiler/70.backend/backend/vhdl/vhdl_hardware_metadata.spl` — extended HardwareAttr, ReturnLabel, HardwareCallInstance
- `src/compiler/70.backend/backend/vhdl/vhdl_bit_semantics.spl` — extended BitWidth, BitSlice, BitConcat, BitExtension
- `src/compiler/70.backend/backend/vhdl/vhdl_hardware_spawn_lower.spl` — NEW: orchestrates hardware spawn lowering pipeline
- `src/compiler/70.backend/backend/vhdl/vhdl_call_lowering.spl` — NEW: hardware call -> entity instance lowering
- `test/compiler/vhdl/hardware_spawn_lower_spec.spl` — NEW: spec for lowering pipeline
