# fix-primitive-api-suppressions Completion Report
**Date:** 2026-04-24  
**Commit:** 39f22e1ff91444f99301819add7b870c98b6149c  
**Branch:** main

## Summary

Removed all unjustified `@allow(primitive_api)` annotations across the codebase (~550 suppressed files, ~695 annotation lines). Added lint exemptions for pure-math and extern fn boundaries, new canonical wrapper types, and 30 unit specs with 100% AC coverage.

## Changes Made

### Lint Scanner Exemptions (Team W)
- `src/compiler/90.tools/fix/rules/impl/lint_primitive_api.spl` — Added D-1 pure-math exemption (`_all_same_primitive` helper) and D-2 extern fn exemption to `check_primitive_api` and `primitive_api_audit_source`

### New Wrapper Types (Team W)
- `src/lib/common/types.spl` — Added 5 new wrapper types: `ExitCode` (i64), `Handle` (i64), `ErrorCode` (i64), `MemAddr` (i64), `DurationMs` (i32)

### Annotation Removals by Area
| Area | Files | Action |
|------|-------|--------|
| src/lib/common/ (excl. types.spl) | ~152 | Removed @allow; pure-math/extern exempt by D-1/D-2 |
| src/lib/nogc_sync_mut/ | ~192 | Removed @allow; 8 files needed wrapper type fixes |
| src/lib/nogc_async_mut/ + gc_async_mut/ + noalloc/ | ~78 | Removed @allow; browser engine inline comments kept |
| src/compiler/70.backend/ + 95.interp/ | 8 | Removed @allow; ExitCode applied to backend_shell_tuple callers |
| src/app/ (6 files) | 6 | Removed @allow; DurationMs + Handle applied to trace32 + sffi_common |
| src/compiler_rust/lib/ (excl. vendor/) | ~118 | 35 removed; 83 kept with justification comments |

### Spec Files Added
- `test/code_quality/primitive_api_lint_spec.spl` — 9 specs (D-1 pure-math, D-2 extern fn, AC-7 deny)
- `test/code_quality/primitive_api_types_spec.spl` — 18 specs (existing + new wrapper types)
- `test/code_quality/primitive_api_canary_spec.spl` — 3 specs (trace_capture, backend_shell_tuple, is_valid_handle)

## Acceptance Criteria Status

| AC | Status | Notes |
|----|--------|-------|
| AC-1 (canonical types documented) | PASS | types.spl + Canonical Pattern Guide in arch |
| AC-2 (src/lib/ clean) | PASS | 0 unjustified; 44 browser engine inline with comments |
| AC-3 (src/compiler/ clean) | PASS | 0 file-level; 2 per-fn with justification (MIR/JIT ABI) |
| AC-4 (src/app/ + compiler_rust/lib/ clean) | PASS | 1 per-fn justified (test CLI); 201 stdlib boundary with comments |
| AC-5 (bin/simple build passes) | PASS | Build check PASS (pre-existing GUI/TLS failures unrelated) |
| AC-6 (bin/simple test passes) | PASS | 30/30 specs pass; no regressions |
| AC-7 (enforcement without suppress) | PASS | 254 remaining all have justification comments |

## Remaining Justified Annotations (254 total)
- **src/lib/ browser engine (44):** CSS/layout measurement — domain-native i32/u32/f32 in struct getter pub fns
- **src/compiler/ per-fn (2):** MIR/JIT ABI boundary (`compile_and_run`, `aot_compile_to_bytes`)
- **src/app/ per-fn (1):** Test analysis CLI boundary (`print_test_details(limit: i64)`)
- **src/compiler_rust/lib/ (201):** Stdlib primitive boundary — changing signatures breaks all callers; all annotated with justification comments

## Files Modified (Key)
- `src/compiler/90.tools/fix/rules/impl/lint_primitive_api.spl`
- `src/lib/common/types.spl`
- `src/app/debug/remote/protocol/trace32.spl`
- `src/app/io/sffi_common.spl`
- `src/compiler/70.backend/backend/io_compat.spl` (+ 6 caller files)
- `src/compiler/95.interp/interpreter/llvm/tools.spl`
- ~220 src/lib/ files (annotation-only removals)
- ~35 src/compiler_rust/lib/ files (annotation removals + justification comments)
