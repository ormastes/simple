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
2. [x] Implement discriminant router in `evaluate_expr` (added `route_expr` fn)
3. [x] Verify `cargo check -p simple-driver` passes (no new errors)
4. [x] Committed — jj auto-snapshot bundled state.md into e533e54c0b and expr.rs into 48bce99ef0; both present in HEAD (dfa5d7716c)

## Semantic Safety Verification (COMPLETED)

All 5 submodules verified safe for O(1) routing:

- **`literals.rs` `Expr::Identifier`**: Never returns `Ok(None)` — ends with `Err(CompileError::semantic_with_context(...))` for unknowns. All positive paths `return Ok(Some(...))`.
- **`calls.rs`**: Explicit arms for all 5 routed variants (`Call`, `KernelLaunch`, `MethodCall`, `FieldAccess`, `FunctionalUpdate`). The `_ => Ok(None)` at line 810 is unreachable from `route_expr`.
- **`ops.rs`**, **`control.rs`**, **`collections.rs`**, **`literals.rs`**: All have `_ => Ok(None)` as final fallthrough, only reachable by variants not routed to them — safe by construction.

`transpose()` converts `Ok(None)` → `None`, so a submodule's `_` arm firing would fall through to the residual `match` in `evaluate_expr` (Spawn, Await, Yield, etc.), preserving correctness.

## Commit note
jj colocated auto-snapshot committed the edits before explicit `jj commit` could run.
The perf changes are split across two commits:
- `e533e54c0b`: `.spipe/interpreter-perf-gaps/state.md` + initial `route_expr` in `expr.rs` (bundled with any+any divergence fix)
- `48bce99ef0`: `.transpose()` refinement to `expr.rs` (bundled with C runtime exclusion fix)

Both changes are in git history. No separate perf commit needed — work is delivered.

## Notes

- The 1460x gap vs C is for fib(30) — tree-walking overhead on pure recursion. Not a
  regression. The cascade fix targets all workloads; Value::Str only matters for string-heavy.
- Native Cranelift is 1.6x C — no bug there.
