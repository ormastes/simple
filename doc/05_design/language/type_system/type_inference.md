# Type Inference Design

> **Superseded for direction (2026-11-27):** this note describes the early
> `simple-type` crate and its "Current State" section is historical. The
> approved rules (inference tiers, implicit generics, `any` only in `unsafe`
> and script mode) are in
> [no_any_inference_generics.md](no_any_inference_generics.md); the staged
> work is in `doc/03_plan/language/type_system/no_any_inference_plan.md`.

## Goals
- Hindley–Milner-style local inference for lets/functions.
- Support pattern matching, arrays, tuples, calls, and builtins (`send`/`recv`/`reply`/`join`/`spawn`).
- Keep compiler/run-time agnostic; inference lives in `simple-type` crate.

## Current State
- `simple-type` implements fresh type vars, unification (shallow), pattern inference, and block inference.
- Builtins registered up front (range/print/len/send/recv/reply/join/spawn).
- No generalization/instantiation yet; no occurs-check.

## Planned Improvements
- Add occurs-check and unify arrays/tuples more precisely.
- Generalize let-bindings; instantiate at use sites for polymorphic functions.
- Carry type annotations on patterns/params through unification.
- Add type schemes for pointer kinds and actor handles once types stabilize.

## Error Strategy
- Report `Undefined` for missing identifiers; `Mismatch` for unification failures.
- Enrich errors with spans (future).

## Testing
- Unit tests in `src/type/tests` for let inference, undefined variables, pattern matches.
- System tests run type checker before evaluation in compiler pipeline.
