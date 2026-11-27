# AOP errors could reach execution or artifact publication

Status: fixed in source; focused native gate probe passed; full pipeline
integration spec remains unrun. Landing is tracked by the associated release PR.

`weave_aop` records validation/conflict/placement failures in `ctx`. JIT and
fixed VHDL orchestration previously continued to their backend, and ordinary
AOT could publish full-inventory success or dispatch a backend despite errors.
Each now returns `CodegenError` with the existing first diagnostic after the
AOP/debug transform phase. No diagnostic is cleared or reclassified as borrowing.

Audited callers: five `weave_aop` callers (ordinary/staged/sharded AOT, JIT, fixed
VHDL) and the explicit-compilation wrapper caller
in `driver_source_llvm_ir`. Staged AOT already compares the batch error count;
sharded AOT and explicit LLVM already gate errors. Their behavior is unchanged.

Validation (2026-11-14): admitted pure-Simple producer SHA
`855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`,
`native-build --runtime-bundle core-c --threads 1`, compiled exact two-line
production gates from all three repaired callers. Twelve native checks passed:
clean context reaches a recording sink; weave, debug, and preexisting-plus-weave
diagnostics prevent it; the first diagnostic survives. Compile and execution
both exited zero. This isolates gate behavior using injected contexts, not the
whole compiler pipeline. Local extraction, source hashes, compiler and execution
logs: `/tmp/aop-gate-native-20261114/`.

The real AOT scenario is in
`test/02_integration/compiler/aop_failure_publication_spec.spl` (UNRUN).
Full compiler/lib/MCP smoke and phase-3 bootstrap were not performed for this
bounded failure-propagation fix. No runtime capability is newly advertised.
