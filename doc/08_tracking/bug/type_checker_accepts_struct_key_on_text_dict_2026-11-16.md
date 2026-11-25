# Type checker accepts a struct as the key of a `Dict<text, _>` index

- **ID:** type_checker_accepts_struct_key_on_text_dict_2026-11-16
- **Priority:** P2. It produced a real Stage 3 blocker: native MIR refused the
  struct key (`E-MIR-STRUCT-DICT-KEY`) only after type checking had already passed.
- **Status:** fixed (2026-11-25). The `Dict(key, value)` arm of the `Index`
  case in `src/compiler/30.types/type_infer/inference_expr.spl` now unifies the
  synthesized index type with the declared key type (non-slice indexes), so a
  struct or otherwise mismatched key is a `TypeInferError.Mismatch` on both
  reads and index-target writes; an unresolved `Infer` key still binds from the
  first index use. Regression/prevention spec:
  `test/01_unit/compiler/type_infer/dict_index_key_type_spec.spl`. The one
  known victim, `AssocTypeResolver` in
  `src/compiler/25.traits/associated_types.spl`, already keys by name text
  (branch `work/assoc-types-text-keys-20261116`, spec
  `test/01_unit/compiler/traits/assoc_type_resolver_text_keys_spec.spl`).

## Symptom
`AssocTypeResolver` declared `traits: Dict<text, SolverTraitDef>` and
`impls: Dict<text, [ImplBlock]>`, but it wrote `self.traits[trait_def.name] = ...`
and `self.impls[impl_block.trait_name] = ...`, where both keys are `HirSymbol`
(an 8-field struct). Type inference reported nothing. The Stage 3 lane only hit
the mismatch in native MIR lowering, and worked around it in 4c9e1062262.

## Minimal repro
```simple
struct Key:
    name: text
    id: i64

class Reg:
    m: Dict<text, i64>

fn main():
    var r = Reg(m: {})
    val k = Key(name: "a", id: 1)
    r.m[k] = 5          # expected: type error, key Key vs text
    print r.m[k]        # expected: type error
```

## Responsible checker code
`src/compiler/30.types/type_infer/inference_expr.spl`, the `case Index(base, index):`
arm of `synthesize_expr` (around line 759). It synthesizes the index type as
`idx_ty` but never uses it for a dict base:

```simple
case Dict(_, value):
    Ok(value)  # Dict doesn't support slicing
```

So the key type is discarded and never unified with `idx_ty`. Assignment through
an index (`case Assign(target, _, value)` in
`src/compiler/30.types/type_infer/inference_control.spl:586`) synthesizes the
target through this same arm. The write side is therefore unchecked too.

## Fix (landed 2026-11-25)
In the `Dict(key, value)` arm, the synthesized `idx_ty` is unified with `key`
and the unify error is returned (non-slice indexes only; the slice path is
unchanged). Existing-call-site impact was measured by running the full
`test/01_unit/compiler/type_infer/` unit suite (the executable consumers of
this checker) plus the lint semantic-check smoke: no existing spec depended on
a loose dict key.

## Evidence
- The mismatch was found by reading the source above. It is now pinned by the
  checker spec `test/01_unit/compiler/type_infer/dict_index_key_type_spec.spl`
  (struct/i64 key on `Dict<text, _>` rejected, text key accepted, write target
  rejected, inferred and generic keys covered).
- The workaround commit 4c9e1062262 (Stage 3 lane) records that the type checker
  accepted the code and MIR refused it.
