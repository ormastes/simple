# enum_assoc_fn_vacuous_spec_sweep

**Date:** 2026-07-28
**Status:** measurement complete — no spec rewrites, no commits

## Question

How many existing specs pass vacuously because of the JIT defect where
`EnumName.assoc_fn(...)` returns a value matching no `case` arm?
(Parent bug: `doc/08_tracking/bug/enum_associated_fn_never_called_on_jit_2026-07-28.md`)

## Answer

**Zero of 13 sampled (8 GENUINE, 5 UNMEASURED).** `bin/simple test` executes
every spec in a child process that hard-sets `SIMPLE_EXECUTION_MODE=interpret`
(`src/app/test_runner_new/test_runner_single.spl:328-329`), and the interpreter
does not have the hijack — it raises `semantic: unknown variant or method ...`,
which is what every GENUINE verdict's evidence shows. The defect is confined to
`bin/simple run` / JIT / native evidence.

**But** the same fact means the spec suite cannot reach the JIT at all, so it is
structurally incapable of catching this bug or any other JIT regression.
Independently confirmed the same day by
`doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md`
(`TestExecutionMode` has no JIT variant; 711 spec files touch divergent
builtins). Treat the two findings as one.

## Population

- 3,867 `EnumName.assoc_fn(...)` call sites (upper bound, 535 files)
- 501 after dropping receiver names shared with a class/struct/trait (lower bound, 99 files)
- 363 of those inside 50 `*_spec.spl` files (27 after removing duplicated legacy test trees)
- 2,507 enum declaration sites / 1,493 distinct enum names / 29,073 variant
  constructions correctly excluded

## Also established (new, worse than the parent bug states)

A **defined** `static fn` on an enum is equally never called under the JIT — not
only undefined ones. Evidence: `build/enum_vacuous_sweep/probe_defined.spl`.

## Artifacts

- Report: `doc/08_tracking/bug/enum_associated_fn_vacuous_spec_sweep_2026-07-28.md`
- Tool + raw data + every run log: `build/enum_vacuous_sweep/` (untracked)
- Mutation script `mutate.shs`, sequential runner `run_sample.shs`

## Working-tree note

`src/lib/common/sdn/value.spl` was already `M` before this lane started (parallel
session). All mutated files were backed up to `build/enum_vacuous_sweep/backup/`
and restored byte-identical afterwards, verified by `diff`.

## Next

Fix belongs in the parent bug, not in the specs: make the JIT's `func_ids` miss
an error instead of a silent fall-through. Re-audit any evidence produced via
`bin/simple run` from the 49 affected non-spec source files — the compiler itself
is among them.
