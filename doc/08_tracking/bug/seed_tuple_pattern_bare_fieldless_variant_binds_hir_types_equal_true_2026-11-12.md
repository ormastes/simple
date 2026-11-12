# Seed: bare fieldless enum variant inside a tuple pattern binds as a catch-all

**Status:** OPEN (found 2026-11-12, aarch64 Linux, by the stage2_if_expr_result_join_untyped_match_payload fix lane)
**Severity:** P1 — silent wrong value in every seed-compiled Stage 2 compiler
**Area:** Rust seed native codegen (tuple-pattern lowering); surfaces in `src/compiler/20.hir/hir_lowering/type_equality.spl:74`

## Repro (seed vs pure-Simple, same source)

```simple
enum Kind:
    Int(bits: i64)
    Str
    Arr(n: i64)

enum Color:
    Red
    Green

fn eq_locals(a: Kind, b: Kind) -> bool:
    match (a, b):
        case (Int(x), Int(y)): x == y
        case (Str, Str): true
        case (Arr(x), Arr(y)): x == y
        case _: false

fn eq_fieldless(a: Color, b: Color) -> bool:
    match (a, b):
        case (Red, Red): true
        case (Green, Green): true
        case _: false

fn eq_qualified(a: Kind, b: Kind) -> bool:
    match (a, b):
        case (Kind.Int(x), Kind.Int(y)): x == y
        case (Kind.Str, Kind.Str): true
        case (Kind.Arr(x), Kind.Arr(y)): x == y
        case _: false
```

| call | seed (`stage2-runtime-authority/simple`, fable-13) | pure-Simple Stage 2 |
|---|---|---|
| `eq_locals(Arr(1), Str)` | **true** | false |
| `eq_locals(Int(1), Int(2))` | false | false |
| `eq_fieldless(Red, Green)` | **true** | false |
| `eq_qualified(Arr(1), Str)` | false | false |
| `eq_locals(Str, Str)` | true | true |

Seed command (from a checkout, entry under it):
`SIMPLE_BOOTSTRAP=1 <seed> native-build --target aarch64-unknown-linux-gnu --backend cranelift --runtime-bundle core-c-bootstrap --source src/lib --entry-closure --threads 8 --cache-dir <d> --mode one-binary --entry build/probe/tupmatch2.spl --runtime-path <stage2-runtime-authority> -o <bin>`.

## Impact on the compiler

`hir_types_equal` matches `(a.kind, b.kind)`; its first bare fieldless arm is
`case (Bool, Bool): true`. Compiled by the seed (which is how every Stage 2
binary is produced), that arm matches any pair the `Int`/`Float` arms did not
take. A probe calling the real `hir_types_equal` (imports
`compiler.hir.hir_lowering.type_equality`) printed, seed-compiled:
`arr_str=true sl_str=true str_arr=true bool_str=true u8_str=true str_str=true arr_arr=true`;
the same probe compiled by the pure-Simple Stage 2 printed `false` for every
mismatched pair. In situ, the seed-compiled Stage 2 MIR join traced
`cmp ok_local=21 arm=27 idx_a=[u8] idx_b=text ... eq=true`.

So on the Stage 2 lane every agreement check built on `hir_types_equal`
(`remember_merged_arm_identity`'s all-typed join, the untyped Ok/Err
constructor join, payload agreement) is silently lax. Stage 3 (pure-Simple
compiled) is not affected.

## Fix options (owner decision)

1. Fix the seed's tuple-pattern lowering so a bare identifier that names an
   enum variant of the scrutinee element type is a variant test, not a binding
   (matches pure-Simple semantics). Root fix.
2. Interim: qualify the bare fieldless arms in `type_equality.spl`
   (`case (HirTypeKind.Bool, HirTypeKind.Bool)` ...). Makes Stage 2 strict at
   once — expect previously-lax joins on the Stage 2 lane to start refusing.
