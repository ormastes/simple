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
