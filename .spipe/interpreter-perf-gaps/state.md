# Interpreter Perf Gaps — State

**Date:** 2026-05-19
**Bug ref:** `doc/08_tracking/bug/interpreter_1460x_c_perf_gap_2026-05-18.md`

## Verified: Already-Done Optimizations

| Bottleneck | Status | Commit |
|---|---|---|
| debug_state mutex → AtomicBool fast-path | DONE — `static DEBUG_MODE: AtomicBool` + Relaxed load | pre-existing (51c85da213) |
| extern dispatch 1080-arm match → HashMap OnceLock | DONE — `EXTERN_DISPATCH: OnceLock<HashMap<&str, ExternFn>>` in `interpreter_extern/mod.rs:46` | fca3f29b05 |

## Remaining Optimization Targets

### 1. Expression cascade (5–10% on all workloads including fib) — IMPLEMENTING
**Location:** `src/compiler_rust/compiler/src/interpreter/expr.rs:182-208`

The `evaluate_expr` function chains 5 sequential `if let Some()` calls, each invoking a
submodule that does a full `match expr { ... }` internally. For the most common expression
types (Call, MethodCall, Binary), this means 1–4 wasted full enum-match traversals before
reaching the correct handler.

**Fix:** Add a discriminant-based early router using a top-level `match expr` that dispatches
directly to the correct submodule, skipping the cascade entirely.

Dispatch table:
- `literals`: Integer, TypedInteger, Float, TypedFloat, Bool, Nil, String, TypedString, FString, Symbol, I18n*, BlockExpr, Identifier
- `ops`: Binary, Unary, New, Cast  
- `control`: Lambda, If, Match, DoBlock
- `calls`: Call, MethodCall, FieldAccess, FunctionalUpdate, KernelLaunch
- `collections`: Array, VecLiteral, ArrayRepeat, Tuple, LabeledTuple, Dict, Range, Index, TupleIndex, Path, StructInit, ListComprehension, DictComprehension, Slice, Spread, DictSpread
- remaining in expr.rs: Spawn, Await, Yield, MacroInvocation, Try, ForceUnwrap, ExistsCheck, UnwrapOr, UnwrapElse, UnwrapOrReturn, Coalesce, OptionalChain, OptionalMethodCall, CastOr, CastElse, CastOrReturn, ContractResult, ContractOld

### 2. Value::Str(String) → Arc<str> (15–25% on string-heavy workloads) — DEFERRED
**Reason:** 780 callsites in owned code. Refactor size disproportionate to gain on the
benchmark workload (fib(30) = pure integer recursion, zero strings). Scoped for a dedicated
PR after bytecode compilation work.

## Implementation Plan

1. [x] Create state.md
2. [ ] Implement discriminant router in `evaluate_expr`
3. [ ] Verify `cargo build --profile bootstrap` passes
4. [ ] Commit with jj

## Notes

- The 1460x gap vs C is for fib(30) — tree-walking overhead on pure recursion. Not a
  regression. The cascade fix targets all workloads; Value::Str only matters for string-heavy.
- Native Cranelift is 1.6x C — no bug there.
