# type_infer_correctness_spec.spl shadows HmInferContext with a 1-field stand-in

**STATUS: RESOLVED 2026-08-10 (spec) — but the rewrite is RED on two newly
exposed product defects, deliberately left failing.**

The shadow was worse than originally filed: besides the 1-field `HmInferContext`,
the spec declared a local text-keyed `HirType` class and an `infer_type(source)`
that was a 20-deep chain of `source.contains("...")` substring matches returning
hand-written results. Every example was testing that string matcher; no product
code ran at all.

Rewritten against the real `HmInferContext` and its Algorithm-W implementation
(`type_infer/core.spl` unify/resolve/occurs, `generalization.spl`
enter_level/exit_level/fresh_var/generalize/instantiate, `context.spl`
bind_mono/lookup) plus the real `DimSolver`. All 13 original example intents were
ported; see "Intent that could not be ported" below for the one framing that
could not survive. Coverage added: arity-mismatch rejection, undefined-name
lookup, a negative occurs-check control, fresh-var-id distinctness, level
tracking, and the dimension solver.

Verdict, both duplicate legs, byte-identical content, measured on a
purpose-built binary (`cargo build --release -p simple-driver`, private
`CARGO_TARGET_DIR`, mtime 2026-08-10 21:41:24 UTC — newer than the 21:31
`checker_check.rs` enum-type-name fix and newer than the deployed
`bin/release/x86_64-unknown-linux-gnu/simple` at 11:06):

`Results: 20 total, 18 passed, 2 failed` (exit 1)

Both failures are real defects in product code, filed with reproductions, NOT
weakened:

- `doc/08_tracking/bug/dim_solver_mismatch_path_calls_span_merge_2026-08-10.md`
  — every dimension-mismatch error path in `dim_constraints.spl` aborts
  (`Span has no field named end`) instead of reporting a `DimError`.
- `doc/08_tracking/bug/dim_solver_try_eval_ignores_substitution_2026-08-10.md`
  — `try_eval` never applies the substitution, so a solved dimension variable
  never evaluates to its bound constant.

Every one of the 18 Hindley-Milner examples passes: unification, substitution
chains, occurs check, level-based generalization, instantiation freshness and
let-polymorphism are all correct once actually exercised.

## Intent that could not be ported

The old spec framed each case as `infer_type("<source text>")`. There is no
source-text entry point on the inference engine — `HmInferContext` operates on
HIR, and reaching it from source requires the full parser + HIR-lowering
pipeline, which is a system-level lane, not a unit spec. Each example's
*semantic* intent was therefore ported to the equivalent HM-level construction
(e.g. "infers identity function type" → generalize `a -> a` and assert exactly
one quantified var with return id == param id; "does not generalize mutable
variables" → the level rule's monomorphic side: a var at the current level is
not quantified, so a second conflicting unification fails). No example was
dropped.

---


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
