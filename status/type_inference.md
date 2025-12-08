# Feature: Type Inference (Feature #13)

- **Importance**: 4/5
- **Difficulty**: 5/5
- **Status**: IN_PROGRESS

## Plan
- Hindley–Milner-style local inference for lets/functions.
- Add type variables, constraints, unification with occurs check in a type checker stage.
- Generalize at let-binding; instantiate at use sites. Report spans on errors.

## Current Work
- Standalone `simple-type` crate drives unification/inference across expressions, arrays, conditionals, and pattern matches (literal/wildcard/guards).
- Compiler runs the type checker before SMF emission to catch undefined identifiers and obvious mismatches.

## References
- Plan: `plans/13_type_inference_generics_gc.md`
- Research: `research/type_inference_generics_gc.md`
