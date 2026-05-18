# SStack State: pure-simple-vhdl-riscv-gap-spawn-plan

## User Request
> next task from the plan — pure_simple_vhdl_riscv_gap_spawn_plan (8 agents: typed metadata, hardware call lowering, bit-width semantics, decode/control, register/ROM/RAM, clock/reset, composite ports, simulation/testbench)

## Task Type
feature

## Refined Goal
> Implement VHDL backend gap-closure infrastructure: typed hardware metadata with return labels, hardware call lowering with port-map composition, fixed-width bit semantics for RV32I fields, decode/control match lowering, register file/ROM/RAM inference models, clock domain/reset policy, composite port flattening, and simulation testbench generation models.

## Acceptance Criteria
- [ ] AC-1: Typed hardware metadata — HardwareAttr + ReturnLabel + MirReturnMetadata with label preservation through AST/HIR/MIR, duplicate label rejection
- [ ] AC-2: Hardware call lowering — HardwareCallInstance + PortMapEntry + VirtualAggregate + CallLowerResult for entity instantiation with deterministic instance names
- [ ] AC-3: Fixed-width bit types — BitWidth + BitSlice + BitConcat + BitDiagnostic for u1-u64 with slice/shift/mask/sign-extend/truncate models
- [ ] AC-4: RV32I instruction fields — InstructionField with opcode/rd/funct3/rs1/rs2/funct7/immediate extraction, I/S/B/U/J format decode models
- [ ] AC-5: Decode/control lowering — MatchCase + AluOp + BranchKind + MemoryOp + DecodeResult for match-to-case synthesis
- [ ] AC-6: Register file/memory inference — RegisterFile + RomInference + RamInference with read/write port config, synthesizability checks
- [ ] AC-7: Clock domain/reset — ClockDomain + ResetPolicy + SequentialState + DomainCrossCheck for process correctness
- [ ] AC-8: Composite ports — PortBundle + FlattenedPort + BusBundle + PortCollisionCheck for struct-to-port flattening
- [ ] AC-9: Simulation/testbench — TestbenchSpec + SourceMapEntry + SmokeProgram + SimulationResult for GHDL verification models
- [ ] AC-10: Verification spec — 20 tests covering all 8 agent areas

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [x] 5-implement (Engineer) — 2026-05-18
- [x] 6-refactor (Tech Lead) — 2026-05-18
- [x] 7-verify (QA) — 2026-05-18
- [x] 8-ship (Release Mgr) — 2026-05-18

## Phase Outputs

### 1-dev
10 ACs across 8 plan agents. Existing: vhdl_builder.spl, VHDL backend in 70.backend/backend/vhdl/.

### 5-implement
5 parallel Sonnet agents. 4 source + 1 test:
- src/compiler/70.backend/backend/vhdl/vhdl_hardware_metadata.spl — HardwareAttr + ReturnLabel + HardwareCallInstance + CallLowerResult
- src/compiler/70.backend/backend/vhdl/vhdl_bit_semantics.spl — BitWidth + BitSlice + InstructionFormat + BitDiagnostic
- src/compiler/70.backend/backend/vhdl/vhdl_decode_memory.spl — AluControl + DecodeResult + RegisterFile + MemoryInference
- src/compiler/70.backend/backend/vhdl/vhdl_clock_ports.spl — ClockDomain + PortBundle + TestbenchSpec + SimulationResult
- test/unit/compiler/vhdl_riscv_gap_spec.spl — 20 tests

### 7-verify
20/20 tests PASS.
