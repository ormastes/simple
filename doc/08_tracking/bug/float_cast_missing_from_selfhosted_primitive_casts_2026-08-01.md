# `float(x)` missing from the self-hosted primitive-cast set

- **Date:** 2026-08-01
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Severity:** medium (loud, module-fatal)
- **Parent:** `selfhost_names_with_no_import_path_masked_by_seed_flat_resolution_2026-08-01.md`
  (carve-out finding 6, `float` in the value namespace)
- **Site:** `src/compiler/20.hir/hir_lowering/expressions.spl`
  `primitive_cast_type_kind`

## Symptom

`unresolved name: float` from `src/std/common/format.spl:103` and `:113`:

```
var frac = f - float(i_part)
...
frac = frac - float(digit)
```

`float` is a builtin **type** name arriving in the **value** namespace. There
is no declaration of `float` anywhere in the tree, so no import could fix it.

## Root cause (PROVED — self-hosted/seed divergence)

The Rust seed treats `float` as an exact alias of `f64` in call position:

```
src/compiler_rust/compiler/src/hir/lower/expr/calls.rs  (lower_utility_builtin)
    "f64" | "float" => Some(TypeId::F64),
```

applied behind an `args.len() == 1` gate, before ordinary name resolution.

The self-hosted `primitive_cast_type_kind` listed only `i8`..`u64`, `f32`,
`f64` and its docstring explicitly excluded `int`/`float`/`bool` as
"value-parsing builtins, not pure numeric casts". For `int` and `bool` that
carve-out is a real design choice; for `float` it was simply a gap, and it
disagreed with the seed. The self-hosted caller applies the same
one-positional-argument gate the seed does, so the two are now identical.

Because the seed's flat resolution never surfaced it, this only appears when
the pure-Simple front end lowers the module.

## Fix

Add `case "float": HirTypeKind.Float(64)` to `primitive_cast_type_kind` and
correct the docstring to record why `float` is in and `int`/`bool` are out,
with the seed line as the authority. `int`/`bool` are deliberately unchanged.

## Regression spec

`test/01_unit/compiler/hir/float_primitive_cast_spec.spl` — the verbatim
`format.spl` shape, a `float(x)`/`f64(x)` equivalence example, and a control
that an unrelated unknown callee still errors loudly.

**Non-vacuity proved by sabotage.** Renaming the new match case to
`"float__sabotaged"` turns the two `float(...)` examples RED (`expected 1 to
equal 0`) while the unknown-callee control stays GREEN. Restoring returns 3/3.

## Verification

Pure-Simple front end interpreted by `bin/simple_seed` (rebuilt 2026-08-01 from
`f93c9b2623`), harness `parse_full_frontend` -> `HirLowering.lower_module`,
asserting on `HirLowering.errors`. Not stage3/stage4.
