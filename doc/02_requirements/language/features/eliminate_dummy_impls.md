# Eliminate Dummy/Stub/Mock Implementations

**Date:** 2026-03-21
**Priority:** P1-P4 (see individual items)
**Status:** In Progress

## Motivation

The compiler codebase contains ~15 dummy/stub/placeholder implementations that silently return wrong results, skip processing steps, or use hardcoded values. Each must be either implemented or explicitly documented as blocked.

---

## Findings

### P1 — Fixed

#### STUB-001: Builder Parser Default
- **File:** `src/compiler/15.blocks/blocks/builder.spl:75`
- **Status:** Fixed — default parser `\payload, _ctx: Ok(BlockValue.Raw(payload))`

#### STUB-002: Effect Inference Not Wired
- **File:** `src/compiler/80.driver/driver_hir_pipeline_lowering.spl`
- **Status:** NOT FIXED — needs an owner ruling (delete vs implement). See
  `doc/08_tracking/bug/effect_pass_dead_and_stub002_falsely_fixed_2026-08-01.md`.
  The previous entry here read *"Fixed — wired `run_effect_pass(self.ctx.hir_modules)`"*.
  That was never true (the pass body was an unconditional early return, and the
  single call site sat in a bootstrap-only branch), and as of 2026-09-02 it names
  a function that no longer exists anywhere in the tree:
  `/usr/bin/grep -rn "run_effect_pass" src/ test/` returns zero hits, and
  `src/compiler/30.types/type_system/effect_pass.spl` has been deleted along with
  both guarding specs (`test/02_integration/compiler/driver/effect_inference_wiring_spec.spl`,
  `test/01_unit/compiler/type_system/effect_pass_spec.spl`). What remains at
  `driver_hir_pipeline_lowering.spl:914` is a comment and a `log_debug` line, not
  a pass. `src/compiler/00.common/effects_solver.spl` (`effectsolver_create`,
  `effectsolver_solve`) is now orphaned — the deleted `effect_pass.spl` was its
  only in-tree consumer.

#### STUB-003: Literal Converter Stubs
- **File:** `src/compiler/70.backend/backend/common/literal_converter.spl`
- **Status:** Fixed — uses `Value.Array()`, `Value.Tuple()`, `Value.Dict()` constructors

### P2 — Fixed

#### STUB-004: Visibility Walk Not Wired
- **File:** `src/compiler/80.driver/driver.spl` + `visibility_integration.spl` + `visibility_checker.spl`
- **Status:** Fixed — dict iteration, method calls, and constructor fixed; wired in driver

#### STUB-005: Monomorphization Not Wired
- **File:** `src/compiler/80.driver/driver.spl`
- **Status:** Fixed — wired `run_monomorphization()` (pass returns identity, safe no-op)

#### STUB-006: CUDA Atomic CAS
- **File:** `src/compiler/50.mir/mir_instructions.spl` + 8 backend files
- **Status:** Fixed — added `GpuAtomicCas` 3-operand MIR instruction, wired lowering, updated CUDA/Vulkan/C/LLVM backends

### P3 — Fixed

#### STUB-007-010: SMF Reader, Template Parsing, Module Loader
- **Status:** Partially fixed — implemented section iteration, length-prefix parsing, GTPL header validation, single-file reader bridge, note.sdn reading. Blocked parts marked with `pass_todo` (FFI section table, full GTPL deserialization, SMF file write-back)

### P4 — Marked with pass_todo

#### STUB-011: im_rs.spl FFI Stubs (25 functions)
- **Root cause:** No Rust FFI bridge built; zero callers
- **Status:** Fixed — all 25 functions marked with `pass_todo("Rust FFI bridge not built")`

#### STUB-012: State Machine / Async Support
- **Root cause:** Requires CPS/state-machine transform + async runtime
- **Status:** Fixed — 13 stub functions marked with `pass_todo` across 4 files. Intentional synchronous fallbacks preserved unchanged

#### STUB-014: Full Monomorphization Engine
- **Root cause:** Requires AST/HIR rewriting engine
- **Action:** Wiring done (STUB-005), full engine is separate major feature

---

## Acceptance Criteria

1. All P1 items fixed with passing tests
2. All P2 items fixed with passing tests
3. P3/P4 items documented for follow-up
4. All existing tests pass after changes

---

## Stub Prevention Requirements

### REQ-PREV-001: Lint Gate in CI

The `stub_impl` lint (STUB001/STUB002) MUST run as part of `bin/simple build check`.
Any STUB001 warning (trivial return with unused params) MUST fail CI.
STUB002 (zero-param default return) is INFO-only but logged.

### REQ-PREV-002: Mandatory pass_todo or pass_do_nothing

Every function body that is intentionally incomplete MUST use `pass_todo("reason")`.
Every function body that is intentionally empty MUST use `pass_do_nothing`.
Bare `pass`, empty bodies, or trivial default returns (0, "", nil, false, []) are
detected by the lint and flagged.

### REQ-PREV-003: Agent Implementation Checklist

During Phase 8 (Implementation) of `/impl`, each code agent MUST:
1. Run `bin/simple build lint` on touched files after implementation
2. Grep for `pass$`, `return 0$`, `return ""$`, `return nil$`, `return false$`, `return \[\]$` in new code
3. Flag any function whose body ignores all parameters
4. Verify no function returns its input unchanged without documented reason

### REQ-PREV-004: Review Agent Stub Scan

During Phase 12 (Duplication Check) of `/impl`, the review agent MUST also:
1. Run `check_stub_impl()` on all new/modified declarations
2. Verify every `pass_todo` has a non-empty reason message
3. Report count of pass_todo vs pass_do_nothing vs implemented functions

### REQ-PREV-005: Identity-Return Detection

Functions that return their input unchanged (e.g., `fn optimize(mir): mir`) without
doing any work MUST be either:
- Marked with `pass_todo("reason")` if they should do work later
- Marked with `pass_do_nothing` if the identity behavior is intentional
- Documented in a comment explaining why the pass-through is correct
