# Native `.to_i64()` on a binop / suffix-literal receiver lowered as a TEXT parse (2026-10-27)

**Status:** FIXED in source (MIR lowering); native proof awaits a compiler redeploy
**Severity:** P1 (silent wrong value, or crash). Root cause of the workaround in
`doc/08_tracking/bug/xxh3_128_hex_all_zeros_native_2026-10-27.md`.

## Repro table (native, `C:/dev/p3new/stage2.exe`, one program per row)
| expression | result | expected |
|---|---|---|
| `(v & 15u64).to_i64()` (v = 0x28241db6188879c2u64) | 0 | 2 |
| `(v >> 4u64).to_i64()` | SEGV | 0x028241db6188879c |
| `(v + 1u64).to_i64()` | SEGV | |
| `(v * 3u64).to_i64()` | SEGV | |
| `(w & 15).to_i64()` (w: i64 = 1234567) | 0 | 7 |
| `.to_u8()` / `.to_u64()` / `.to_i32()` on u64 and i64 binops | correct (2, 2, 2, 7, 1234568, 1234568) | |
| `val v = 0x..u64` then `"{v.to_i64()}"` | SEGV | decimal value |

Only `to_i64` (and `to_int`) miscompile. The narrowing conversions have their own Cast arm
(`method_calls_literals.spl` conv_narrow) that does not depend on the receiver proof.

## Root cause
`to_i64`/`to_int` is also a TEXT builtin. In `method_calls_literals.spl`
`erased_receiver_text_builtin` (about line 2500-2540) admits a receiver as "erased text" when
`receiver.type_` is nil/Infer/Any and `local_is_proven_numeric_scalar` is false. That predicate
refuses I64/U64 MIR locals without a HIR Int type (because `Any` also lives in an I64 local), and a
binop temp, a `Cast` expression, and a `val v = 5u64` local (suffix literals are
`Cast(IntLit, u64)` after the flat-AST bridge, `convert_nodes.spl:1297`) carry no HIR type. So the
call lowered to `rt_string_new/rt_string_len/rt_string_to_int_lenient` fed the raw integer word:
a small word returns 0, a large one is dereferenced as a pointer (SEGV). A plain `v: u64`
parameter has a HIR type, which is why `v.to_i64()` worked.
Second site: the numeric arm at `method_calls_literals.spl:~4854` used the same predicate, so even
past the text arm it fell to `rt_to_int_dynamic`.

## Fix
- `method_calls_literals.spl`: text-builtin exclusion and the numeric `to_i64` arm also accept
  `builtin_numeric_expr_kind(receiver) != 0`; `local_is_proven_numeric_scalar` accepts U64 MIR locals.
- `builtin_method_extras.spl`: `builtin_numeric_expr_kind` no longer returns early with 0 when
  `enum_match_expr_type` gives a non-numeric type, treats `& | ^ << >>` over integers as integer, and
  treats `Cast` to a numeric type as that kind; `builtin_remember_numeric_init` records the 64-bit
  Int type of `val v = <expr as/suffix u64>`.

## Evidence
Spec `test/01_unit/compiler/50.mir/to_i64_binop_receiver_spec.spl` runs the real HIR+MIR lowering
in the interpreter and asserts no `rt_string_to_int_lenient` callee. Before the fix all 5 numeric
cases emitted `rt_string_new, rt_string_len, rt_string_to_int_lenient`; after, none do, and an
`Any` receiver still does (6/6 pass). `builtin_method_extras_lowering_spec` (22) and
`builtin_method_table_sweep_spec` (23) pass; `builtin_method_extras_guard_spec` has one failure
(`Result.ok() over a struct payload`) identical with and without this change.

## Native proof
NOT done: `C:/dev/p3new/stage2.exe` is a pre-built compiler binary and does not read
`src/compiler` at `native-build` time, so the fix only takes effect after the compiler is rebuilt
and redeployed. The `as i64` / `as u8` workaround in `src/lib/common/crypto/xxh3.spl` is left in
place; removing it waits on that redeploy plus a native re-check of `xxh3_128_hex`.

## Interpolation crash
Same cause (`val v = 0x..u64` has no HIR type, so `v.to_i64()` became a text parse of the raw
word). Fixed by the same change at the lowering level; the native re-check is pending the redeploy.
