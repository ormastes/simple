# Strict no-GC ownership admission and checker policy

A successfully admitted strict module makes ownership checking mandatory for its
entire compile context. Selecting `--no-borrow-check` then produces
`NOGC-POLICY-002`; remove the option and repair the reported ownership error.
Legacy-only contexts retain the explicit diagnostic bypass.

The authority is the typed admission result in
`src/compiler/80.driver/driver_hir_pipeline_support.spl`, after physical source
policy and HIR policy agree. `CompileContext.nogc_ownership_required` retains the
fact across HIR eviction and subsequent batches. A legacy entry with a strict
dependency therefore cannot disable checking. A new context starts false;
a later failed or legacy-only admission cannot downgrade a context already
admitted as strict. Failed admission remains fatal and publishes no new policy.

The AOT seam is exercised by
`test/01_unit/compiler/driver/aot_borrow_gate_fail_closed_spec.spl`. Typed policy
publication is covered by
`test/01_unit/compiler/semantics/param_effects/driver_nogc_param_effect_gate_spec.spl`.
Both need execution by an admitted pure-Simple full runtime; this source change
has no Stage 4 qualification receipt yet. A Stage 2 compiler build alone does not
qualify public test/check/docgen or the deployed CLI.

This rule closes the explicit checker-option bypass. It does not establish
common HIR move/drop checking on every interpreter route, deterministic cleanup
on every runtime, or completion of the no-GC recovery plan.

## Typed HIR interpreter preflight (source implementation, not yet qualified)

The pure CLI fallback is cli_run_file → interpret_file → CompilerDriver Interpret
→ InterpreterBackendImpl. It now validates every retained module before the first
execution, and direct backend calls validate before constructing Environment. The
layer55 HIR adapter emits CFG Read/Move/Write/Revive into the same OwnershipFlow solver
used by MIR NLL. Contract, recursion and work failures reject strict execution.

Supported flow includes assignment, return, aggregate construction, if/elif,
while/loop, labeled exits and exact local parameter-effect call contracts. Forms
without a complete adapter (including match/pattern binding, exception cleanup,
async suspension, indirect calls and short local alias transfer) are explicitly
refused in strict mode; this is incomplete language support, not acceptance.
Legacy compatibility remains unchanged. No target MIR or second source parse is
created. Driver/backend checks currently repeat bounded validation to protect
direct callers until immutable checked-HIR authority can remove the repetition.

For actual route evidence set SIMPLE_OWNERSHIP_TEST_RUNTIME to the exact admitted
full CLI and run test/02_integration/compiler/ownership/hir_ownership_preflight_spec.spl.
The negative fixture must fail with moved-use evidence and no entry marker; the
exclusive-path positive must execute successfully. Both remain NOT_EXECUTED.

The standalone core AST interpreter/inprocess probe, explicit bootstrap driver
override, fork-mode Rust adapter and cached/direct SMF loaders are separate
authorities. This change does not qualify those routes, cleanup or the full
44-row recovery plan.

The live imported-call path retains compact frozen source/body/effect receipts and
verifies providers once before execution. Package-internal context must originate
in canonical admission, never deserialized user metadata. The direct public
backend refuses imported ownership without that context. Reconciliation source
review is clean, conditional on the separately reviewed current codec integration.
Runtime resource qualification remains NOT_RUN.

2026-11-07 reconciliation status: prior review4 addressed the direct ingress
ordering issue statically. The current release codec is reconciled independently
to preserve newer declarations; bounded traversal is a required integration
dependency. The memory lane preserves current driver changes and imports only
the strict ownership context/admission fields. All execution evidence remains
NOT_RUN until an exact current producer is admitted; prior source review is not
runtime qualification.
