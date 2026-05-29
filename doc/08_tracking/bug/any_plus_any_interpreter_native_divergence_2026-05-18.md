# BUG: ANY+ANY semantic divergence between interpreter and native codegen

**Date:** 2026-05-18
**Status:** BLOCKED — fix in commit `e533e54c0b` is incomplete (see verification section below)
**Severity:** Low (no known user-facing breakage)
**Related fix:** 5054eb144c — native `+` operator in non-main functions

## Problem

When both operands of `+` have `TypeId::ANY` (untyped function parameters), interpreter and native codegen behave differently:

- **Interpreter**: runtime dispatch — `1 + "x"` → string concat `"1x"`, `1 + 2` → arithmetic `3`
- **Native (Cranelift)**: always emits `iadd` — `1 + "x"` → garbage (integer add on pointer), `1 + 2` → correct `3`

## Root cause

The fix in `lowering_expr_ops.rs` removed `TypeId::ANY` from `is_string_add` to fix `+` in non-main functions. This was correct — `ANY` should NOT unconditionally route to `rt_string_concat`. But it means `ANY + ANY` now always becomes `iadd` in native mode.

## Impact

- **Current**: No known breakage. All stdlib `+` uses are on typed operands.
- **Future**: If users write `fn add(a, b): return a + b` and call with mixed types, interpreter and native will diverge.

## Proposed fix

Emit a runtime type-check branch for `ANY + ANY` in native codegen:
```
if is_string(left) || is_string(right):
  call rt_to_string(left), rt_to_string(right), rt_string_concat
else:
  iadd left, right
```

This requires runtime type tags, which may not be available in Cranelift AOT yet. Lower priority until polymorphic dispatch is needed in native mode.

## Fix (e533e54c0b, 2026-05-19)

Three-part change:

1. **`src/runtime/runtime.h`** — declared `rt_any_add(int64_t left, int64_t right) -> int64_t`
2. **`src/runtime/runtime_native.c`** — implemented `rt_any_add`: checks whether either operand
   is a heap-tagged string via `rt_core_as_string`; if so, delegates to `rt_string_concat`;
   otherwise returns `left + right` (integer arithmetic on tag-zero INT values is safe because
   TAG_INT=0x0 so tag bits cancel under addition).
3. **`src/compiler_rust/compiler/src/mir/lower/lowering_expr_ops.rs`** — when
   `op == BinOp::Add && left.ty == TypeId::ANY && right.ty == TypeId::ANY`, emits
   `MirInst::Call { rt_any_add }` before the `is_string_add` block instead of falling through
   to `MirInst::BinOp { iadd }`.

The interpreter path (`ops.rs` L631–L664) already dispatches correctly by matching on
`Value::Str` at runtime; the fix brings native codegen to parity.

### Residual gap: ANY+STRING / STRING+ANY (one typed, one untyped)

The `is_string_add` block (L65–L107) fires when at least one operand is `TypeId::STRING`.
When `left.ty == TypeId::ANY` and `right.ty == TypeId::STRING`, the string-concat path is
taken (correct). However `left.ty != TypeId::STRING && left.ty != TypeId::ANY` is `false`
for the ANY case, so `rt_to_string` is NOT called on the ANY side — it is passed raw to
`rt_string_concat`. This is safe as long as `rt_string_concat` handles non-string first
arguments, but it may produce unexpected coercion behaviour. Lower priority; no regression
from prior state.

## Workaround (pre-fix)

Add type annotations to function parameters: `fn add(a: int, b: int)` or `fn concat(a: text, b: text)`.

## Behavioral Verification (2026-05-29) — Status: BLOCKED

### Test program

```
fn add(a, b):
    return a + b

fn main():
    print(add(1, 2))      # expect 3 in both modes
    print(add(1, "x"))    # expect "1x" in both modes
```

### Results

| Mode       | `add(1, 2)` | `add(1, "x")` |
|------------|-------------|----------------|
| Interpreter | `3` (correct) | `1x` (correct) |
| Native (before runtime lib surgery) | link error: `undefined symbol: rt_any_add` | link error: `undefined symbol: rt_any_add` |
| Native (after adding `rt_any_add` to deployed lib) | (blank — likely wrong) | `<value:0x1>x` (wrong) |

Note: the blank native output for `add(1,2)` was not separately verified but is
also expected to be wrong (raw untagged int `1` used in arithmetic may produce
garbage or `0` depending on the code path).

Contrast confirming root cause:
- `add(8, "x")` → `1x` (correct — `8 = 1 << 3` is a properly tagged integer)
- `add(1, "x")` → `<value:0x1>x` (wrong — raw untagged integer `1` passed to `rt_any_add`)

### Root cause (deeper than the original fix)

Two layered problems:

**Problem 1 — `rt_any_add` missing from deployed runtime library.**
Commit `e533e54c0b` added `rt_any_add` to `src/runtime/runtime_native.c` and
`src/runtime/runtime.h`, but the deployed `bin/release/libsimple_runtime.a`
was never rebuilt. The deployed native compiler could not link `rt_any_add`.
The fix was present in source but not in the binary.

**Problem 2 — Integer literals passed untagged to ANY-typed parameters.**
The self-hosted codegen (in `src/compiler/`) does not insert a `BoxInt`
(tag-the-integer) instruction when passing a typed integer literal as an
argument to a function whose parameter has type `ANY`. The tag encoding is
`(n << 3) | 0x0` for integers. A raw untagged `1` has low bits `001 = TAG_HEAP`,
so `rt_core_as_string(1)` returns a garbage pointer rather than null, causing
`rt_string_concat(1, "x")` → `rt_to_string(1)` → `<value:0x1>`.

The Rust seed codegen (seed analog, for reference) at
`src/compiler_rust/compiler/src/mir/lower/lowering_expr_call.rs:50-53`
builds `arg_regs` via `lower_expr` but inserts `BoxInt` only for specific
paths (enum variant payloads, array push). Direct calls to user functions with
`ANY` params do not box their integer args. The self-hosted `.spl` compiler
(`src/compiler/`) has the same gap — confirmed by behavioral divergence, but
the exact `.spl` call-lowering site was not confirmed during this investigation.
(To find it: `grep -r 'box_int\|BoxInt\|rt_any_add' src/compiler/` in the
self-hosted tree.)

### Investigation note

`bin/release/libsimple_runtime.a` was mutated during investigation via
`ar -r` with a locally-compiled `runtime_native_new.o` and
`runtime_memtrack_new.o` (plain `cc -O2`, not the build system flags).
These files are not git-tracked. A full `scripts/bootstrap/bootstrap-from-scratch.sh --deploy`
is required to regenerate authoritative deployed libraries.

### Proper fix (blocked)

Insert `BoxInt` for integer-typed args to ANY-typed function parameters in
the self-hosted compiler codegen (`src/compiler/` `.spl` tree), then run a
full bootstrap redeploy. This is a broad call-site change with regression risk
and is deferred. Rule: "fix in `.spl` not Rust" applies, and the change is
beyond the scope of this task.

### Status

The original commit `e533e54c0b` was incomplete:
- Interpreter path: correct (already worked)
- Native path: diverges at any call to a function with `ANY` params and
  integer literal args (pre-existing untagged-arg bug, not gated by `rt_any_add`)

Workaround still applies: annotate parameters with concrete types.
