# An untyped function's result is erased to `0` (or to `value << 3`)

**Date:** 2026-08-01
**Status:** Open
**Severity:** High — silent wrong data, no error
**Area:** Rust seed (`src/compiler_rust/target/bootstrap/simple run`), Any-erasure
at the call boundary

## Symptom

When a function has **no declared return type**, its trailing-expression value
is read back by the caller as `0`. When its **parameters** are untyped but the
return type is declared, an indexed read comes back as the raw tag-boxed word
(`value << 3`). Only the fully-annotated form is correct.

Found while root-causing
`doc/08_tracking/bug/byte_at_reads_zero_from_slice_result_2026-07-28.md`, where
`fn byte_at(data, index):` returned `0` for every input.

## Repro

```
fn no_ret_type(data: [i64], index: i64):
    data[index]

fn with_ret_type(data: [i64], index: i64) -> i64:
    data[index]

fn untyped_params_ret_i64(data, index) -> i64:
    data[index]

fn main():
    val block: [i64] = [7, 8, 9]
    val a: i64 = no_ret_type(block, 1)
    val b: i64 = with_ret_type(block, 1)
    val c: i64 = untyped_params_ret_i64(block, 1)
    print(a.to_text())   # 0   — WRONG, expect 8
    print(b.to_text())   # 8   — correct
    print(c.to_text())   # 64  — WRONG, 8 << 3 (raw tag-boxed word)

main()
```

Measured with the Rust seed
(`src/compiler_rust/target/bootstrap/simple run`) on 2026-08-01.

## Notes

- Comparison operators on untyped params are **not** affected — a separate
  probe of `if a >= b` with untyped `a`/`b` returned correct results.
- The `value << 3` form is the same tag-boxed-word family as
  `reference_list_get_returns_value_shifted_left_3`.
- Because the erased value is a legal `0`, callers silently take a wrong
  branch; there is no error or warning.

## Impact

Any library written with untyped helper signatures decodes as zeros at the call
boundary. The TLS wire helpers hit this; other untyped-helper modules should be
audited.

## Fix

Root-cause the Any-erasure path so an undeclared return type infers the
trailing expression's type instead of dropping the value, and so an untyped
parameter's indexed read is unboxed before returning. A/B against the
interpreter, JIT, and native engines.

## RE-VERIFIED 2026-08-17 — STILL LIVE, reproduced on a freshly built seed

Seed built from current `src/compiler_rust` (`BUILDRC=0`, binary 2026-08-17
08:15). Probe: `test/01_unit/compiler/codegen/probe_any_typed_value_consumption_jit.spl`.

    SIMPLE_EXECUTION_MODE=jit
      FAIL untyped_fn_result_add got=<value:0x5> want=5
      FAIL untyped_fn_result_id  got=<value:0x7> want=7
    SIMPLE_EXECUTION_MODE=interpreter
      PASS untyped_fn_result_add
      PASS untyped_fn_result_id

Refinement of the title: the result is NOT erased to zero. The correct value
IS present (`0x5` is 5, `0x7` is 7) but its static type is `TypeId::ANY`, so
the value reaches the rendering site still TAGGED and prints `<value:0x..>`
instead of the number. Same silent-wrong-result class, different mechanism —
the boxing is never undone rather than the value being lost.

Fixture shape (`fn untyped_result(a: i64, b: i64): return a + b` — no declared
return type). The interpreter is correct because it decodes the tag
dynamically per value; the JIT makes the decision statically and has no type
to make it from.

Not fixed in this pass: unlike the chained-builtin sibling below, there is no
per-callee name to classify — the fix is to infer the return type from the
body's return expressions in `hir/lower/type_resolver.rs`, or to emit a
dynamic `UnboxInt` (now total via `rt_value_unbox_int`) at the consumption
site. Both are larger than a lookup-table entry and were not attempted here.

Detection spec: `test/01_unit/compiler/codegen/any_typed_value_consumption_class_spec.spl`
(the `renders an untyped function result as a number` example is RED by design
until this is fixed).
