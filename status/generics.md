# Feature: Generics (Feature #14)

- **Importance**: 4/5
- **Difficulty**: 5/5
- **Status**: IN_PROGRESS

## Plan
- Parse generic params on functions/types; generic args on calls/usages.
- Instantiate generics with fresh type vars; monomorphize with instantiation cache; mangle symbol names.
- Integrate with type inference and future trait bounds.

## Current Work
- `simple-type` crate provides the type-variable/unification substrate we will use for generic instantiation; parser already accepts generic type forms.
- Monomorphization and bound checking still pending.

## References
- Plan: `plans/13_type_inference_generics_gc.md`
- Research: `research/type_inference_generics_gc.md`
