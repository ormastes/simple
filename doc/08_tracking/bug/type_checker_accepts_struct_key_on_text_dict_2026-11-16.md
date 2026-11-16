# Type checker accepts a struct as the key of a `Dict<text, _>` index

- **ID:** type_checker_accepts_struct_key_on_text_dict_2026-11-16
- **Priority:** P2. It produced a real Stage 3 blocker: native MIR refused the
  struct key (`E-MIR-STRUCT-DICT-KEY`) only after type checking had already passed.
- **Status:** open. The checker is not fixed. The one known victim,
  `AssocTypeResolver` in `src/compiler/25.traits/associated_types.spl`, now keys
  by name text (branch `work/assoc-types-text-keys-20261116`, spec
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

## Expected fix (not done here)
In the `Dict(key, value)` arm, unify `idx_ty` with `key` and return the unify
error. Before making it fatal, measure how many existing call sites it would
flag, because other code may depend on loose dict keys.

## Evidence
- The mismatch was found by reading the source above. It is not yet a checker
  spec, and no dedicated checker run was done for this record.
- The workaround commit 4c9e1062262 (Stage 3 lane) records that the type checker
  accepted the code and MIR refused it.
