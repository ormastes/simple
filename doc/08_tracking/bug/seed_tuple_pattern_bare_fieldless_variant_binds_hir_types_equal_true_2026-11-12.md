# Seed: bare fieldless enum variant inside a tuple pattern binds as a catch-all

**Status:** FIXED in the seed (2026-11-12, work/bug-seedtuplepat-20261112) — found 2026-11-12, aarch64 Linux, by the stage2_if_expr_result_join_untyped_match_payload fix lane
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

## Root cause (2026-11-12)

Not native-codegen-specific: the seed's HIR lowering, shared by `native-build`
and the `run` JIT. A top-level `case Red:` goes through
`lower_pattern_condition_stmt` (`hir/lower/stmt_lowering.rs`), which tests
`subject_enum_has_variant(subject_ty, name)`. A bare name in a SUB-pattern goes
through `subpattern_condition` (`hir/lower/expr/control.rs`), which listed
`Pattern::Identifier(_)` among the irrefutable patterns, and the element slots
built by `sequence_element_slots` are ANY-typed, so there was no type to test
against. `collect_pattern_bindings` already used the tuple element / array
element / enum payload field types to EXCLUDE such names from the arm's
bindings, so the arm neither bound nor tested the name. The tree-walk
interpreter (`interpreter_patterns.rs`, value-driven) was already correct.

Fix (seed only; `type_equality.spl` untouched):

- `subpattern_condition_typed(slot, slot_ty, ..)`: a bare `Identifier` that is
  a unit variant of `slot_ty`'s enum emits `rt_enum_check_variant`, as the
  top-level arm does. `Typed`/`Or`/nested `Tuple`/`Array`/enum payloads pass
  the declared type down.
- `sequence_condition_typed`: element `i` of a `HirType::Tuple`, or the
  `HirType::Array` element type.
- `nested_payload_condition` takes the outer enum + subject type and types
  each payload slot with the same `get_enum_variant_field_types_with_hint`
  call `collect_pattern_bindings` makes (`case Box(Red):` had the same defect).
- `bind_subpattern` only writes names the arm actually binds: before, a bare
  variant `Green` with an outer local `val Green = 99` in scope overwrote that
  local with the slot value.

Rules: a bare name is a variant test iff the slot's declared enum owns it as a
variant; a capitalized name that is NOT a variant of the slot's enum (e.g. a
variant of another enum) still binds, as on pure-Simple (which warns; the seed
interpreter refuses it); pattern names never consult outer locals, so the
variant wins over a same-named local and that local is left untouched.

Fixture: `test/fixtures/compiler/tuple_pattern_bare_unit_variant_native.spl`
(exit 0 = pass). Seed HIR test:
`test_bare_unit_variant_in_sub_pattern_is_variant_test`
(`hir/lower/tests/control_flow_tests.rs`).

| probe (aarch64) | unfixed seed native | unfixed seed `run` (JIT) | seed tree-walk interp | fixed seed native / JIT | run-14 Stage 2 native |
|---|---|---|---|---|---|
| repro table + negatives (20 rows) | 11 wrong | 11 wrong | 0 wrong | 0 wrong / 0 wrong | 0 wrong |
| payload slot / shadow / arrays (11 rows) | 7 wrong | — | 0 wrong (9 rows; `(Red, Relaxed)` refused) | 0 wrong | 2 wrong (arrays) |
| real `hir_types_equal` mismatched pairs (5) | all `true` | — | — | all `false` | see PR |
| fixture | exit 1 | — | — | exit 0 | — |

Still open, separate from this fix: the pure-Simple frontend does not type
ARRAY pattern elements (`lower_match_pattern_with_union_v1` handles
`PatternKind.Tuple` only), so `case [Red, _]:` over `[Color]` binds `Red` as a
catch-all in Stage 2/3 — the seed (fixed) and the interpreter test it. Struct
field sub-patterns in the seed are still untyped (`struct_fields_condition`).
Behavioural consequence: Stage 2 compilers built by the fixed seed run
`hir_types_equal` strictly, like Stage 3; previously-lax agreement checks on
the Stage 2 lane can now refuse.
