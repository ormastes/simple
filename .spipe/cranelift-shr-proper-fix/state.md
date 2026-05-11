# SStack State: cranelift-shr-proper-fix

## User Request
> Fix Cranelift right-shift (>>) semantics for all integer widths. Current interim fix only handles narrow signed ints partially. Need full right-shift for var-load, param, and call-ret paths. See doc/03_plan/remaining_roadmap.md item 3 (C.2).

## Task Type
bug

## Refined Goal
> Ensure right-shift (`>>`) produces correct results for all integer types (i8/i16/i32/i64, u8/u16/u32/u64) across all value origins — variables, function parameters, and call return values — in both Cranelift and LLVM backends. Add test coverage for the parameter and return-value paths.

## Acceptance Criteria
- [ ] AC-1: `>>` on signed function parameters (i8/i16/i32) uses arithmetic shift (sshr) with proper sign-extension
- [ ] AC-2: `>>` on signed call return values uses arithmetic shift with proper sign-extension
- [ ] AC-3: LLVM backend dispatches signed vs unsigned right-shift (currently always unsigned)
- [ ] AC-4: New spec tests cover: signed param >> N, signed call-return >> N, unsigned param >> N
- [ ] AC-5: Existing `shr_signedness_test.spl` still passes (no regression)
- [ ] AC-6: `cargo test` in compiler crate passes

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-11
- [ ] 2-research (Analyst)
- [ ] 3-arch (Architect)
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
**Task type:** bug
**Feature slug:** cranelift-shr-proper-fix

**Analysis:**
- Interim fix (FR-DRIVER-0002b, 2026-04-18) correctly handles local variable right-shift by capturing signedness before `coerce_binop_operands` widens operands
- Gap 1: Function parameters arrive pre-widened; if `vreg_types` doesn't track their original signedness, shift dispatch defaults to unsigned
- Gap 2: Call return values may lose signedness metadata similarly
- Gap 3: LLVM backend (`llvm/instructions.rs:244`) always uses unsigned `build_right_shift(..., false)` — no signed dispatch

**Key files:**
- `src/compiler_rust/compiler/src/codegen/instr/core.rs` (lines 234-273) — ShiftRight dispatch
- `src/compiler_rust/compiler/src/codegen/cranelift_emitter.rs` — ensure_i64_typed sign-extension
- `src/compiler_rust/compiler/src/codegen/llvm/instructions.rs` (lines 243-245) — LLVM shift
- `src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs` — MIR signedness tracking
- `test/unit/compiler/shr_signedness_test.spl` — existing test

**Agent plan:**
- Agent A (Phase 2+3): Research signedness flow through params/returns, design fix
- Agent B (Phase 5): Implement fixes in core.rs + llvm/instructions.rs + add tests
- Agent C (Phase 7): Verify all paths

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
