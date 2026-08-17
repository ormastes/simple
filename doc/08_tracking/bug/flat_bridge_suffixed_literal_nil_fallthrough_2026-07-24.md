# Bug: FlatAstBridge dropped EXPR_SUFFIXED_LIT — every `5i32`-style literal compiled as tagged-nil (3)

- **Date:** 2026-07-24
- **Severity:** P0 wrong-code — silent, type-checked, affects every suffixed numeric literal on the flat-AST lane
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).

## Symptom

NVMe rv32 fw gate booted but printed `FAIL`; fail bitmask 361 = sections
rain/map/sched/pt/queue_phase. Interp reference of the same logic: `fail=0`.

Object-level probe (riscv32-unknown-none, LLVM backend):

| Source | Emitted |
|---|---|
| `val w: i32 = 5` | `li a0, 5` ✓ |
| `val w = 5 as i32` | `li a0, 5` ✓ |
| `val w: i32 = 5i32` | `li a0, 3` ✗ |
| `val w: i64 = 5i64` | `li a0, 3` ✗ |
| `-1i32 as i64` | `-3` ✗ |
| `0i32 - 1i32` | `0` (3-3) ✗ |

Every suffixed literal became the constant **3** — the tagged RuntimeValue nil.
XOR-only tests still passed (3^3 cancels), which is why the gate's synthetic
single-section mode stayed green while real sections failed.

## Root cause

`convert_flat_expr` (flat AST pool → legacy `Expr`) had **no arm for
`EXPR_SUFFIXED_LIT` (tag 36)**; the node fell into the final
`else: NilLit` — the same silent-drop pattern previously fixed for
`EXPR_CAST` (see the comment on that arm). The nil literal then lowered to the
tagged-nil constant 3 at collection/ABI boundaries.

The parser side was always correct (`expr_suffixed_int` stores the parsed
value + suffix); only the bridge dropped it.

## Fix

New arm lowers `NiSUFFIX` exactly like the equivalent cast the pipeline already
handles: `5i32` → `Cast(IntLit(5), Named("i32"))`, `2.5f32` →
`Cast(FloatLit(2.5), Named("f32"))`.

## Lessons / follow-ups

1. The `else: NilLit` fall-through in `convert_flat_expr` has now silently
   swallowed at least two node kinds (Cast, SuffixedLit). It should `print` a
   `[flat-bridge] unhandled expr tag=<n>` diagnostic (the `tag <= 0` branch
   already does) instead of silently producing nil. TODO left to a follow-up.
2. Regression test: compile-and-objdump (or run) a suffixed-literal probe on a
   cross target; assert constant equals the literal.
3. Related session fixes needed to expose this: seed at 906b85d1420
   (seed_interp_defer_lazy_imports_module_globals_2026-07-24.md), text.spl
   `contains` UFCS recursion, MirLowering `fn_return_types` ctor omission,
   gate ABI ilp32d→ilp32 + libgcc for `__divdi3`/`__moddi3`.
