# Native: `v == nil` is true for the integer 3 (both backends) and for bool `true` (LLVM) on non-optional scalars

**Status:** root cause FIXED in source on `work/rel-native-nil-compare-20261010`
(MIR lowering + LLVM backend); takes effect only in a REBUILT stage 2. Not yet
verified on a rebuilt stage 2 (see "Verification on the next rebuild").
**Engines:** staged-native (stage 2 and later), both `--backend llvm` and
`--backend cranelift`; also the seed's default JIT `run` lane. The tree-walk
interpreter (`SIMPLE_EXECUTION_MODE=interpret`) is the oracle and is correct.
**Found via:** `HirCodecWriter.put_i64` / `put_bool`
(`src/compiler/20.hir/hir_codec_support.spl`) writing `N` for 3 and for true,
so the stage-2 HIR cache never hit
(`hir_codec_put_i64_three_encoded_as_nil_native_2026-10-10.md`, which only
works around it in the codec).

## Root cause

1. **MIR lowering** (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`,
   Binary `Eq`/`NotEq` arm, the `case _:` fall-through after the
   Optional/`rt_is_none` routing): the `nil` literal is materialized as the raw
   word **3** (`case NilLit` — `rt_core_nil()` = SPECIAL tag 0b011, payload 0).
   For an operand whose static type is a NON-optional scalar nothing routed the
   compare anywhere, so it fell through to the generic `emit_binop(Eq, v, 3)`:
   a plain i64 slot holding 3 compared equal to the sentinel. Same raw compare
   in `??` (`case NullCoalesce`: `rt_is_some(v)` on payload bits) and in `.?`
   (`case ExistsCheck`, which is what the parser desugars `if val x = v:` into).
2. **LLVM backend** (`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`,
   `translate_binop` `case Eq`/`case Ne`): the compare ran at the LEFT
   operand's LLVM type. A `bool` param is `i1`, so the i64 constant 3 was
   `trunc`'d to i1 = **1**, and `true == nil` was true while `nil == true` was
   false. Cranelift keeps Bool as a uniform i64, so it had only defect 1.

## Native evidence (frozen stage 2 `simple-bootstrap 1.0.0-rc.1`, src @6b540f21546)

Probe: `fn i64_eq(v: i64) -> bool: v == nil` and friends (full program below).
`exp` = tree-walk interpreter (`SIMPLE_EXECUTION_MODE=interpret`).

| line | exp | llvm (before) | cranelift (before) |
|---|---|---|---|
| `i64_eq(0,1,3,11,19)` | `false false false false false` | `false false true false false` | `false false true false false` |
| `i64_eq_rev(3,4)` (`nil == v`) | `false false` | `true false` | `true false` |
| `i32_eq(3,4)` / `u8_eq(3,4)` | `false false` | `true false` | `true false` |
| `bool_eq(false,true)` | `false false` | `false true` | `false false` |
| `bool_eq_rev(false,true)` | `false false` | `false false` | `false false` |
| `i64_ifval(3,4)` | `some(3) some(4)` | `none some(4)` | `none some(4)` |
| `i64_coalesce(3,4)` (`v ?? 99`) | `3 4` | `99 4` | `3 4` |
| `ret` (`r3==nil rt==nil ret3()==nil ret_true()==nil`) | `false false false false` | `true true true true` | `true false true false` |
| `field` (`bx.i bx.b bx.f ==nil; bx.i bx.b !=nil`) | `false false false true true` | `true true false false false` | `true false false false true` |
| `elem` (`[1,3,11]` + `[false,true]` `==nil`) | `false false false false false` | `false true false false true` | `false true false false false` |
| `local` (`lit3==nil litt==nil lit3!=nil litt!=nil`) | `false false true true` | `true true false false` | `true false false true` |

Also observed in the same probe, **not fixed here** (separate Option
representation defects, both backends unless noted):
`opt_i64_eq(nil)` false (exp true); `opt_bool_eq(nil)` false (exp true);
`opt_i64_ifval(make_opt(3))`/`(make_none())` both `none` (exp `some(3)`/`none`);
cranelift only: `val ov: i64? = 3; ov == nil` true and `val ob: bool? = true;
ob == nil` true (LLVM correct). These need their own records once re-measured
on a stage 2 built from current source (14 commits touched `50.mir` since
6b540f21546).

## Fix

- `nil_compare_operand_is_plain_scalar` (expr_dispatch.spl): operand is a
  non-optional primitive scalar by STATIC type (HIR `Int`/`Float`/`Bool`/`Char`
  from the type-checker annotation, else the lowering's own declared-local
  registry — params, annotated bindings, `[T]` element reads), its MIR local is
  a primitive scalar, and it is not tracked as an Option handle, nil literal or
  tagged runtime value. Then:
  - `v == nil` folds to `false`, `v != nil` to `true` (both operand orders);
  - `v ?? d` is `v` (default not evaluated, as in the interpreter);
  - `v.?` is `v`, so `if val x = v:` takes the present branch with `x = v`.
  Optional-typed, text, enum, struct and untyped/Any operands are untouched and
  keep `rt_is_none`/`rt_is_some`/`rt_native_eq` (they can carry a real nil).
  The Optional detection now also consults the declared-local registry.
- `equality_compare_type` (core_codegen.spl): Eq/Ne with an `i1` left and a
  wider integer right compares at the integer's width (zext the bool).
- Cranelift needs no backend change (uniform-i64 Bool); it is fixed by the MIR
  fold.

Specs (interpreted, fail-before / pass-after):
`test/01_unit/compiler/mir/scalar_nil_compare_folds_to_constant_spec.spl`
(5 examples: 8 int widths x `==`/`!=`, bool/f32/f64/char both orders, local /
field / element / call-result operands, `if val` + `??`, and the negative
matrix for `i64?`/`bool?`/`f64?`/text/enum/struct) and
`test/01_unit/compiler/backend/llvm_bool_int_equality_width_spec.spl`
(IR text: `zext i1` + `icmp eq i64`, no `trunc ... to i1`).

## Exposure in the compiler's own source (release/1.0 tree)

Direct scalar-typed param/local compared with nil: 5 sites, all in the HIR
codec — `src/compiler/20.hir/hir_codec_key_order.spl:48-50` (`left: i64`,
`right: i64` — a key-ordering comparator, so any 3 mis-ordered) and
`hir_codec_support.spl:361,367` (worked around on the sibling branch). Field
reads `x.<field> == nil` where some struct declares `<field>` as a non-optional
scalar: 269 textual sites (compiler 208 / app 34 / lib 27) — an UPPER bound,
dominated by overloaded names (`type_` 49, `span` 46, `kind` 15, `generation`
15, `symbol` 13) whose matching struct field is usually a handle, not a
scalar. None of the 0 sites in `src/app`/`src/lib` is a direct scalar
param/local compare.

## Verification on the next rebuild

Rebuild stage 2 from this source, then compile and run the probe below with
BOTH backends. Every `*_eq` line must be all `false`, `*_ne` all `true`,
`i64_ifval: some(3) some(4)`, `i64_coalesce: 3 4`, `ret: false false false
false`, `field: false false false true true`, `elem:` all `false`, `local:
false false true true`. Then re-check the HIR cache: a second identical build
must report `[hir-cache] hits == modules`.

```simple
struct Box:
    i: i64
    b: bool
    f: f64

fn i64_eq(v: i64) -> bool:
    v == nil
fn i64_ne(v: i64) -> bool:
    v != nil
fn i64_eq_rev(v: i64) -> bool:
    nil == v
fn i32_eq(v: i32) -> bool:
    v == nil
fn u8_eq(v: u8) -> bool:
    v == nil
fn bool_eq(v: bool) -> bool:
    v == nil
fn bool_ne(v: bool) -> bool:
    v != nil
fn bool_eq_rev(v: bool) -> bool:
    nil == v
fn f64_eq(v: f64) -> bool:
    v == nil
fn i64_ifval(v: i64) -> text:
    if val x = v:
        "some({x})"
    else:
        "none"
fn i64_coalesce(v: i64) -> i64:
    v ?? 99
fn ret3() -> i64:
    3
fn ret_true() -> bool:
    true

fn main():
    print "i64_eq: {i64_eq(0)} {i64_eq(1)} {i64_eq(3)} {i64_eq(11)} {i64_eq(19)}"
    print "i64_ne: {i64_ne(0)} {i64_ne(3)} {i64_ne(11)}"
    print "i64_eq_rev: {i64_eq_rev(3)} {i64_eq_rev(4)}"
    print "i32_eq: {i32_eq(3)} {i32_eq(4)}"
    print "u8_eq: {u8_eq(3)} {u8_eq(4)}"
    print "bool_eq: {bool_eq(false)} {bool_eq(true)}"
    print "bool_ne: {bool_ne(false)} {bool_ne(true)}"
    print "bool_eq_rev: {bool_eq_rev(false)} {bool_eq_rev(true)}"
    print "f64_eq: {f64_eq(3.0)} {f64_eq(1.5)}"
    print "i64_ifval: {i64_ifval(3)} {i64_ifval(4)}"
    print "i64_coalesce: {i64_coalesce(3)} {i64_coalesce(4)}"
    val r3 = ret3()
    val rt = ret_true()
    print "ret: {r3 == nil} {rt == nil} {ret3() == nil} {ret_true() == nil}"
    val bx = Box(i: 3, b: true, f: 3.0)
    print "field: {bx.i == nil} {bx.b == nil} {bx.f == nil} {bx.i != nil} {bx.b != nil}"
    val arr: [i64] = [1, 3, 11]
    val barr: [bool] = [false, true]
    print "elem: {arr[0] == nil} {arr[1] == nil} {arr[2] == nil} {barr[0] == nil} {barr[1] == nil}"
    val lit3: i64 = 3
    val litt: bool = true
    print "local: {lit3 == nil} {litt == nil} {lit3 != nil} {litt != nil}"
```

Expected output (identical on llvm and cranelift):

```
i64_eq: false false false false false
i64_ne: true true true
i64_eq_rev: false false
i32_eq: false false
u8_eq: false false
bool_eq: false false
bool_ne: true true
bool_eq_rev: false false
f64_eq: false false
i64_ifval: some(3) some(4)
i64_coalesce: 3 4
ret: false false false false
field: false false false true true
elem: false false false false false
local: false false true true
```

Build recipe used for the before-measurement (Windows, frozen stage 2):
`simple.exe native-build --target x86_64-pc-windows-msvc --backend <llvm|cranelift>
--runtime-bundle core-c-bootstrap --runtime-path <stage2-runtime-authority>
--entry-closure --entry <probe.spl inside the checkout's src/> --mode one-binary
--output probe.exe`, with `SIMPLE_SCV_INVENTORY_COLD_INIT=1 SIMPLE_WINDOWS_ABI=msvc
SIMPLE_LINKER_FLAVOR=msvc CC=clang-cl.exe` (and `tools/` present in the
checkout — `counterpart_abi_runtime.c` includes a header from there).

## Related

- `native_i64opt_some0_collapses_to_nil_2026-07-14.md` (why nil is 3, not 0)
- `native_tagged_nil_prints_as_integer_3_in_i64_sink_2026-08-18.md`
- `pure_simple_option_i64_ifval_always_some_eqnil_always_false_2026-08-08.md`
- `hir_codec_put_i64_three_encoded_as_nil_native_2026-10-10.md` (sibling branch)
