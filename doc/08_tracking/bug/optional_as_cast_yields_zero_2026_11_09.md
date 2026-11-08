# `as <int>` on an optional returned from a function silently evaluates to 0

- **id:** optional_as_cast_yields_zero_2026_11_09
- **status:** fix-implemented-verification-pending (seed + self-hosted HIR lowerer)
- **severity:** P2 — silent wrong value; masked a spec red for two months
- **found:** 2026-11-09, diagnosing `acpi_spec_three_reads_return_zero_2026-09-19` (PR #7884)

## Symptom

```simple
fn mk(v: u64) -> u64?:
    if v != 0:
        v
    else:
        nil

val r = mk(0xFED00000)
expect(r ?? 0).to_equal(0xFED00000)   # passes
expect(r as u64).to_equal(0xFED00000) # FAILS: expected 0 to equal 4275044352
```

Measured 2026-11-09 on the deployed Windows seed `bin/simple.exe` (2026-11-04), both lanes:

| lane | `mk(4275044352) as u64` |
|------|-------------------------|
| interpreter (no `main`) | `0` |
| JIT (`fn main`) | `4929918024849` (a reinterpreted heap word) |

A locally typed optional did NOT reproduce on the interpreter (`val r: u32? = 0xB008;
r as u32` gives `0xB008`) because the interpreter stores a present local optional as
its bare payload; only a function-returned (boxed `Option.Some`) value hits the bug.

## Expected

Per nil-only-in-unsafe (memory `nil-only-in-unsafe`, ERR-01), `T?` must be narrowed
with `?? default`, `if val x = ...` or `match` before use as `T`; `T? as T` outside
`unsafe` is a compile error. Silently yielding 0 satisfied every `to_be_nil`-style
assertion and turned real payloads into zeros.

## Root cause (seed, `src/compiler_rust`)

- `hir/lower/expr/operators.rs::lower_cast` performed no admissibility check: any
  `expr as T` lowered to `HirExprKind::Cast` typed `T`. The JIT then reinterpreted the
  boxed Some word.
- `interpreter/expr/casting.rs::cast_to_numeric` has an "enum variant -> ordinal" arm;
  a boxed `Value::Enum { enum_name: "Option", variant: "Some", .. }` matched it and
  the cast returned the position of `Some` (0).

## Fix

Seed:
- `lower_cast` rejects `T? as <numeric>` (both HIR spellings: registry optional and
  the builtin `Option<T>` enum) when `FunctionContext.unsafe_depth == 0`, with
  `LowerError::OptionalCast`. The message carries the `SIMPLE_JIT_STRICT:` marker so
  `exec_core.rs` cannot demote the module to the interpreter instead of failing.
- `lower_unsafe_block` maintains `unsafe_depth` (decremented on both exits).
- `cast_to_numeric` rejects a boxed `Option` with a type-mismatch error (fail-closed
  twin for the tree-walking lane).

Self-hosted (`src/compiler/20.hir/hir_lowering`):
- `expression_core.spl` Cast arm emits `[E-OPT-CAST-001]` when the operand's HIR type
  is `Optional(_)`, or — since this lowerer types few expressions — when the operand is
  a named local/parameter or a call of a named function whose DECLARED symbol type is
  `Optional(_)` (`cast_operand_declared_type`), the target is `Int`/`Float`, and
  `unsafe_block_depth == 0` (new capability-agnostic counter on `HirLowering`,
  maintained in the `UnsafeBlock` arm).

## Tests

- cargo `hir::lower::tests::expression_tests::optional_as_numeric_cast_is_rejected_outside_unsafe`
  (RED before: lowered fine; GREEN after) — function-returned `T?`, local `T?`, float
  target, `Option<i64>` spelling, `?? 0` narrowing admitted, `unsafe:` admitted,
  depth restored after the block, plain numeric cast untouched.
- cargo `interpreter::expr::casting::optional_cast_tests::boxed_option_some_to_numeric_is_an_error_not_zero`
  (RED before: `UInt { value: 0 }`; GREEN after).
- spec `test/01_unit/compiler/hir/optional_as_cast_rejected_spec.spl` (self-hosted
  lowerer; RED on unmodified source: `expected 1, got 0` x2).
- Seed built from this branch: interpreter lane now errors
  `type mismatch: cannot cast an optional T? to u64`; JIT lane now errors
  `HIR lowering error: SIMPLE_JIT_STRICT: cannot cast an optional ...` (no fallback).

## Callers surfaced by the corpus

553 candidate files (mixing `as <int>` with `?` types) lowered with the fixed seed:
3 hits, all the same idiom over `json_to_number(...) -> any?`
(`if item == nil: missing else: item as i64`), in
`src/app/spipe_knowledge_provider/{document_binding,wire_json,durable_records}.spl`
— rewritten to `(item ?? missing) as i64`. `test/01_unit/os/acpi/acpi_test.spl` on
origin fails 3 examples with the new error — exactly the sites PR #7884 rewrites to `??`.
The `bytes[i] as i64` index-cast idiom is not affected (0 hits).

Fixing those callers exposed a second seed gap: `lower_coalesce` kept an `any?`
subject typed as the optional pointer (only scalar / `text?` inners were narrowed), so
`(any? ?? d) as i64` was itself rejected. `any? ?? d` is now typed `any` — the payload
word of an erased optional is the tagged RuntimeValue an `any` slot holds, and MIR only
unboxes scalar-typed `rt_unwrap_or_self` results, so no representation changes.

## Residual (separate record)

Inside `unsafe:` the JIT's `r as u64` on a boxed `Some` still yields a garbage word
(`6219716837105`) — see `jit_unsafe_optional_as_cast_garbage_2026_11_09`.

## Related

- `acpi_spec_three_reads_return_zero_2026-09-19.md` — the symptom this hid.
