# An untyped function's result is erased to `0` (or to `value << 3`)

## Re-measured 2026-09-13 — HALF FIXED, entry stays OPEN on the remaining half

Binary: Rust seed `build/vt4/bootstrap/simple.exe` (Windows), the entry's own
repro run verbatim as a whole program with `main()` appended.

| lane | `no_ret_type` (a) | `with_ret_type` (b) | `untyped_params_ret_i64` (c) |
|---|---|---|---|
| default (JIT) | **0 — still WRONG** | 8 | **8 — now CORRECT** |
| `SIMPLE_NO_JIT=1` | **0 — still WRONG** | 8 | 8 |
| `SIMPLE_EXECUTION_MODE=interpret` | **8 — CORRECT** | 8 | 8 |

Two things this pins down that the original report could not:

1. **The `value << 3` half is FIXED.** Case (c) — declared return type, untyped
   parameters — returned the raw tag-boxed word `64` when filed; it now returns
   `8` on every lane. That sub-defect can be treated as closed.
2. **The remaining half is a JIT/MIR-only divergence, not a language-wide
   erasure.** The Rust AST interpreter gets case (a) right. Only the JIT and the
   `SIMPLE_NO_JIT=1` (MIR) path erase a *missing return type annotation* to `0`.
   That narrows the search to the return-type-inference/erasure decision on the
   MIR lowering path, and gives a free differential oracle: any candidate fix can
   be checked against `SIMPLE_EXECUTION_MODE=interpret` on the same file.

Still **silent wrong data, no error** — severity unchanged.

**Not fixed here:** lives in `src/compiler_rust/**`, off-limits during this pass
(concurrent bootstrap; editing Rust sources aborts it).


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
