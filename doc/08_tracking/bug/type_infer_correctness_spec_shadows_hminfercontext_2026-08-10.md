# type_infer_correctness_spec.spl shadows HmInferContext with a 1-field stand-in

- **File**: `test/unit/compiler/type_infer/type_infer_correctness_spec.spl:133-137,318`
- **Real product code**: `src/compiler/30.types/type_infer_types.spl:178-198`
- **Found during**: bounded first pass on `spec_shadow_reimplementation_worklist.tsv`

## What's wrong

The spec declares a local `HmInferContext` with a single field (`next_id`),
constructed via `HmInferContext.new()` → `HmInferContext(next_id: 0)`. The
real `HmInferContext` (a `struct`, not `class`) has 4+ fields:
`env: TypeEnvironment`, `level: i64`, `next_var: i64`,
`subst: Substitution`, plus dimension-constraint-solver fields for
tensor/layer type checking (per its own docstring). The spec's Hindley-Milner
level-based generalization and dimension-solver logic — the entire stated
purpose of the real type — is untested; the spec only exercises whatever
local logic it built around a bare integer counter.

## Why not fixed in this pass

Same class of finding as the `narrowing_spec` and `riscv_dual_arch_spec`
shadows filed alongside this one today: real fix requires constructing a
`TypeEnvironment`/`Substitution` fixture and rewriting assertions against the
real level/dimension-solver behavior — a real rewrite, not a bounded import
swap.

## Unblock condition

Rewrite against the real `HmInferContext` struct in
`src/compiler/30.types/type_infer_types.spl`, including at least one
exercise of level-based generalization (`enter_level`/`exit_level` or
equivalent) and the dimension solver, not just field presence.
