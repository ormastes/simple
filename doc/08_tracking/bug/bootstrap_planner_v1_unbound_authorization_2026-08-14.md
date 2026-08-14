# Bootstrap planner v1 unbound authorization

Status: OPEN — v2 source contract is fail-closed; no admitted producer exists

The version-1 planner receipt authorized any target with a bootstrap or release
prefix and bound only a typed reason. It did not identify the admitted parent
compiler, its sanity/provenance evidence, frozen runtime, planner source
closure, git state, build command/environment, cache scope, planner executable,
planner smoke, or authorization artifact. A copied or stale receipt therefore
could not prove which inputs had been planned.

Planner admission v2 replaces prefix admission with the two exact targets
`//bootstrap:stage3` and `//bootstrap:stage4` and a target-specific reason set.
Its authorization content binds the parent compiler, runtime snapshot, source
closure, and planner hashes. The enclosing canonical receipt binds all frozen
evidence using unique ordered fields and exact lowercase SHA-256 values.
Canonical nonsymlink paths, mutation rejection, and runtime-plus-closure cache
scope are checked structurally by
`scripts/check/lib/bootstrap-planner-admission-bound.shs`. Structural validity is
not authority: the public verifier deliberately rejects every body until an
independently admitted Stage 2 parent can build and execute the planner under
an owned pre-exec lock and bind exact argv, environment, stdout, exit status,
derivation receipt, and smoke evidence. The unsafe shell body publisher was
removed.

Focused negative evidence is
`test/01_unit/scripts/bootstrap_planner_admission_bound_contract_test.shs`; the
pure-Simple source boundary is covered by
`test/01_unit/compiler/bootstrap_reason_planner_admission_source_contract_spec.spl`.
Neither test builds or runs a planner. Operational closure still requires an
admitted parent, a built planner, a real smoke receipt, and a resulting v2
admission before any bootstrap stage starts.
