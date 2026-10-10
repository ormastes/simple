# Match guards dropped by the if-chain desugaring (tuple / text / range / struct / array arms)

Status: FIXED in source (this change), not native-verified. Severity: P1
(silent wrong code). Found 2026-10-10 by robustness item 3a.

## What

`HirLowering.build_if_chain`
(`src/compiler/20.hir/hir_lowering/_Expressions/match_desugaring.spl`) lowers
every `match` whose arms are not all MIR-native into nested `if`. It built the
test from the pattern only and never read `arm.guard`, so

```simple
match (a, b):
    case (1, y) if y > 10: 1
    case (1, y): 2
    case _: 3
```

returned `1` for `(1, 2)` on the stage-2 path (seed: `2`). No diagnostic. The
same held for text-literal, range, struct and array arms.

Separately, a guard on an int-literal / binding / wildcard arm of a non-enum
match was a hard error (`match guards (case x if cond:) are not supported by
native codegen yet (B5b Phase 2)`), i.e. loud, not wrong code.

## Live sites (single-file census, pre-fix lowering with the invariant on)

38 of the 41 files under `src/` that contain a guard were measured (108
textual guarded arms); 3 could not be lowered by the harness (seed
`HirImportItem has no field kind`: `70.backend/backend/cuda_backend.spl`,
`95.interp/execir.spl`, `95.interp/mir_interpreter.spl`).

| Site | Dropped |
|---|---|
| `src/compiler/30.types/type_infer/core.spl` `unify` | 2 guards: `(Int(b1, s1), Int(b2, s2)) if b1 == b2 and s1 == s2`, `(Float(b1), Float(b2)) if b1 == b2` -- ints / floats of different width unified |
| `src/app/interpreter/utils/collection_ops.spl:200` `bind_sequence_pattern` | 1 guard: `case "Tuple" if allow_tuple:` |

(The other seven guards of `unify` are unreachable for a different reason:
`bare_unit_variant_in_tuple_pattern_binds_2026-10-10.md`.)

## Fix

- `build_if_chain` tests `pattern and { destructure prelude; guard }` (`and`
  short-circuits in MIR, so the prelude never runs on a rejected value).
- `MirLowering.lower_guarded_scalar_match` lowers guarded int / or-of-int /
  binding / wildcard arms in source order and traps when no arm accepts.
- The guard-count invariant (`E-HIR-MATCH-GUARD` / `E-MIR-MATCH-GUARD`, rule
  advisory id `E-MIR-MATCH-GUARD`) reports any guard parsed but not lowered. With the fix the census
  is 0 hits; with the if-chain fix reverted it reports exactly the two sites
  above.

Specs: `test/01_unit/compiler/50.mir/match_guard/`.
Guide: `doc/07_guide/compiler/robustness/match-guard-invariant.md`.
