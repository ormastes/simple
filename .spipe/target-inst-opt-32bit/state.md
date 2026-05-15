# SStack State: target-inst-opt-32bit

## User Request
> impl and improve optimization plugin by plan - doc/01_research/local/target_instruction_optimization_32bit.md, doc/01_research/domain/target_instruction_optimization_32bit.md, doc/02_requirements/feature/target_instruction_optimization_32bit_options.md, doc/02_requirements/nfr/target_instruction_optimization_32bit_options.md, doc/04_architecture/target_instruction_optimization_32bit.md, doc/05_design/target_instruction_optimization_32bit.md, doc/03_plan/sys_test/target_instruction_optimization_32bit.md, doc/06_spec/app/compiler/feature/target_instruction_optimization_32bit_spec.spl, doc/03_plan/agent_tasks/target_instruction_optimization_32bit.md

## Task Type
feature

## Refined Goal
> Implement the target instruction optimization plugin (Option B: target matrix + x86-64 32-bit-form optimization) with NFR Option 2 (correctness + x86-64 non-regression), extending the existing MIR optimization pipeline and backend lowering to support per-target instruction families with legality/profitability gates, starting with x86-64 narrow-form selection and scaffolding for x86-32, AArch64, ARM32, RV64, and RV32.

## Acceptance Criteria
- [ ] AC-1: `TargetFamily` enum covers X86_64, X86_32, Aarch64, Arm32, Rv64, Rv32 with triple-parsing that correctly classifies each
- [ ] AC-2: `InstructionFamily` + `TargetEnableMatrix` correctly enables/disables families per target, returning `FamilyDecision` with reason and fallback
- [ ] AC-3: x86-64 32-bit-form legality prover accepts narrow u32/i32 values and rejects pointer truncation or unknown-width operands
- [ ] AC-4: Optimization planner flow (parse triple → build feature set → evaluate matrix → legality → profitability → dispatch) is wired into the existing `pipeline_optimize` path
- [ ] AC-5: Golden MIR/lowering tests pass for each enabled instruction family on x86-64, with at least unsupported-feature rejection tests for other targets
- [ ] AC-6: x86-64 optimized benchmark kernels produce same-or-smaller `.text` size and same-or-faster runtime vs baseline (within 3% noise)
- [ ] AC-7: All existing BDD spec tests in `target_instruction_optimization_32bit_spec.spl` pass

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-15
- [ ] 2-research (Analyst)
- [ ] 3-arch (Architect)
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
Task type: **feature**. Refined from 9 plan documents into Option B (target matrix + x86-64 32-bit-form optimization) with NFR Option 2 (correctness + non-regression gates). 7 acceptance criteria defined covering target family classification, enable matrix, legality proofs, planner integration, golden tests, benchmark gates, and BDD spec compliance. Scope: ~15-25 files across `60.mir_opt/`, `70.backend/`, and test fixtures.

### 2-research
<pending>

### 3-arch
<pending>

### 4-spec
<pending>

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
