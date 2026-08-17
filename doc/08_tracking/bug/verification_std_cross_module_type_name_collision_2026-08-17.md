# Cross-module type-name collision: `ContractExpr`/`ContractExprKind` resolve to the wrong module

**Date:** 2026-08-17. **Status:** OPEN (spec left RED by policy).

## Symptom
`test/00_formal_verification/compiler/unified_attrs_spec.spl` — 2 of 5 examples RED:

- `semantic: unknown variant or method 'Forall' on enum ContractExprKind`
- `semantic: unknown static method call on class ContractExpr`

Both symbols exist and are correctly declared in
`src/compiler_rust/lib/std/src/verification/models/contracts.spl`
(`ContractExprKind.Forall` at line 38; `static fn call` at line 442).

## Root cause
Two modules in the co-compiled closure both define `ContractExpr` and
`ContractExprKind`:

- `.../verification/models/contracts.spl` (has `Forall`, `static fn call`)
- `.../verification/lean/contracts.spl` (line 188 enum has NO `Forall`; line 217
  class has no `call`)

When the spec imports `verification.models.contracts as contracts` while
`verification.lean.contracts` is also loaded, alias-qualified member access
(`contracts.ContractExprKind.Forall`) resolves against the **lean** module's
same-named types. This is the type-level sibling of the known
`compiler_cross_module_private_symbol_collision` warning (which the runner
already prints for duplicate `fn` names, but not for classes/enums).

## Repro
`bin/simple test test/00_formal_verification/compiler/unified_attrs_spec.spl`
→ `Results: 5 total, 3 passed, 2 failed` (the two errors above).

Control: `lean_workflow_spec.spl` uses the same models API but does not import
both contract modules under aliases, and passes 9/9.

## Unblock condition
Interpreter/semantic module-alias resolution must key class/enum lookup by the
aliased module, not by a global type-name table (or the two `ContractExpr`
families must be renamed apart). When fixed, the 2 RED examples in
`unified_attrs_spec.spl` go green with no spec edit.

## Related same-day fixes (separate defects, fixed)
- Static-factory drift in the verification std tree (instance `fn` called
  statically): fixed by promoting to `static fn` in `models/contracts.spl`,
  `models/memory_capabilities.spl`, `proofs/checker.spl`,
  `proofs/obligations.spl`, `lean/verification_checker.spl`.
- Dead `host.process` import + nonexistent `.success`/`fs.exists` in
  `verification/toolchain.spl`: repointed to `std.process` / `fs.exist`.
- Reproducing specs: `tool_checker_spec.spl`, `memory_capabilities_spec.spl`,
  `toolchain_detection_spec.spl`, `lean_workflow_spec.spl`,
  `unsupported_construct_spec.spl`, `lean_block_integration_spec.spl` (all green).
- Generalization spec:
  `test/00_formal_verification/compiler/verification_std_api_generalization_spec.spl`
  (6/6 green) — probes adjacent static factories and toolchain import health.
- Still latent, same family: `verification/lean/runner.spl` imports
  `host.process.{monotonic_ms, ProcessResult, run}` (3-arg `run`, `monotonic_ms`
  have no std.process equivalent) and `verification/lean/proof_ref.spl` imports
  `io.fs.list_dir` which the resolved io.fs dict does not provide. Only
  exercised when a Lean toolchain is present.

## Resolution (2026-08-17, later same day)

**REPRODUCED before fixing**, on the deployed binary:

    Results: 5 total, 3 passed, 2 failed

with the two documented errors, plus the compiler's own diagnostic naming both
files and prescribing the remedy verbatim:

> warning: class `ContractExpr` has 2 co-compiled definitions across 2 modules;
> the interpreter resolves class members by NAME across modules ... Defined in:
> `.../verification/lean/contracts.spl`, `.../verification/models/contracts.spl`.
> **Rename one of the classes to a unique name.**
> `[compiler_cross_module_private_symbol_collision]`

**Fix taken: the rename, not an interpreter change.** A census of the two
families showed the `lean/contracts.spl` pair is a self-contained duplicate with
**no external consumers**: every other module — including `lean/expressions_eval.spl`,
which sits in the same package — already imports `ContractExpr`/`ContractExprKind`
from `verification.models.contracts`. The only outside reference was
`lean/__init__.spl:82`, which re-exported the *wrong* family. So the lean pair
was renamed to `LeanContractExpr` / `LeanContractExprKind`
(`src/compiler_rust/lib/std/src/verification/lean/contracts.spl`, 55 sites; the
`__init__.spl` export updated to match).

**Not fixed here (deliberately):** the underlying interpreter behaviour — class
and enum member lookup keyed by a global type-name table rather than by the
aliased module — is unchanged. It is out of this lane's file scope, and it
remains a live latent hazard for any future same-named pair. The "Unblock
condition" section above still describes the real compiler-side fix.
