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
- **File:** `src/compiler/80.driver/driver.spl`
- **Status:** Fixed — wired `run_effect_pass(self.ctx.hir_modules)`

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
- **File:** `src/compiler/50.mir/mir_instructions.spl` + backends
- **Status:** Deferred to follow-up (agent changes lost to jj reset)

### P3 — Deferred

#### STUB-007-010: SMF Reader, Template Parsing, Module Loader
- **Status:** Deferred to follow-up session

### P4 — Blocked / Future Design

#### STUB-011: im_rs.spl FFI Stubs (25 functions)
- **Root cause:** No Rust FFI bridge built; zero callers
- **Action:** Add pass_todo markers in follow-up

#### STUB-012: State Machine / Async Support
- **Root cause:** Requires CPS/state-machine transform + async runtime
- **Action:** Synchronous fallback is intentional for interpreter

#### STUB-014: Full Monomorphization Engine
- **Root cause:** Requires AST/HIR rewriting engine
- **Action:** Wiring done (STUB-005), full engine is separate major feature

---

## Acceptance Criteria

1. All P1 items fixed with passing tests
2. All P2 items fixed with passing tests
3. P3/P4 items documented for follow-up
4. All existing tests pass after changes
