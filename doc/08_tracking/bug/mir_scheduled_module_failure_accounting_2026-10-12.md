# MIR scheduled module failure accounting

The retained direct lowering loop emitted `failed=0` even after actual MIR
lowering appended fatal diagnostics. The no-source fallback loop emitted no
classified progress rows. The new common accounting helper alone did not
connect either actual loop to progress reporting.

Each scheduled unit now captures the previous context error count and MIR
diagnostic boundary. Only new fatal diagnostics, newly recorded context
errors, or its ICE classify that unit as failed. Multiple fatal diagnostics
still remain separate ordered diagnostics and count as one failed module.
Warnings remain successful. Early ICE, transient-scope failure and
E-MONO-038 rejection publish the completed classification before returning.
The collector and progress classification share the unchanged explicit-fatal
or legacy-message predicate. No diagnostic is removed, rewritten or downgraded.

`test/fixtures/bootstrap/mir_module_failure_classification_probe.spl` has
eight numbered guard groups using the actual unsupported-expression recovery
owner, cumulative lowerer diagnostics and common failure accounting. It
covers explicit fatal errors, duplicate diagnostics in one module, a subsequent
warning-only module, the preserved legacy fallback and an empty diagnostic
suffix. All eight groups are **UNRUN**. Source review and whitespace checking
do not qualify the native producer or progress output.

The forthcoming archived production consumer must use this same predicate and
one classification per genuine scheduled emission unit. The fixed bootstrap
shortcut and existing demand/cache admission policies are unchanged.
