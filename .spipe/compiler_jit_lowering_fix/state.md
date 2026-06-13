# Feature: compiler_jit_lowering_fix

## Raw Request
perf and others fix on both compiler and os (goal 2026-06-13): every spec run logs "JIT compilation failed, falling back to interpreter: HIR lowering error: Unknown variable: decorator while lowering skip" (also "Unknown type: Lexer") — spec files never JIT.

## Task Type
bug

## Refined Goal
Spec files JIT-compile instead of silently falling back to the interpreter: the HIR lowering failure on std.spec's skip/decorator symbols is root-caused and fixed in pure Simple, with measured spec-runtime before/after.

## Acceptance Criteria
- AC-1: Root cause documented in the state file: which symbol(s) fail HIR lowering and why (std.spec skip decorator path, Lexer type reference).
- AC-2: Fix in pure Simple (src/compiler/** or src/lib/common/spec*/std.spec) eliminates the "Unknown variable: decorator while lowering skip" fallback on a fixed spec set (test/01_unit/lib/http_server/*, test/01_unit/os/fs_exec_fallback_contract_spec.spl); the INFO fallback line no longer appears for that cause.
- AC-3: Before/after wall-clock timing on the fixed spec set recorded honestly (if JIT does not improve time, record the real numbers and why).
- AC-4: Full touched-area regression: the 240-example sweep from the hardening wave stays green; bin/simple check clean on touched files.
- AC-5: If the root cause turns out to live in the Rust seed only, STOP, document precisely, and record a bug doc instead of patching Rust (Fix .spl not Rust).

## Scope Exclusions
No Rust seed changes. No new JIT features — fix the lowering failure only.

## Phase
dev-done

## Log
- dev: Created state file with 5 acceptance criteria (type: bug)
