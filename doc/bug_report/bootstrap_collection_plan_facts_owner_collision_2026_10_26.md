# Bootstrap CollectionPlanFacts owner collision

Status: OPEN. Tagged source workaround: unique guarded selection owner.

The provisional P3 full05 run failed natively in MIR owner 20. Immutable
`build/verify/provisional-p3-future-constructor-object-20261025-05/logs/p3-build.log`
lines 248497-248498 report an unresolved operator on `HirPerfEffectFacts` at
`perf/collection_plan_explain.spl:31:61` and `:35:65`, where source compares
`facts.profile_hash_probes_p95 >= 0` and `facts.profile_hash_collisions_p95 >= 0`.
Both counters are declared `i64` in `perf/collection_plan_selection.spl`.

The immediately preceding collision diagnostic retains the existing
`perf/collection_plan.spl::CollectionPlanFacts` field list, whose first field
is `effects: HirPerfEffectFacts`, over the unrelated guarded selector's
`CollectionPlanFacts` field list. This explains the erroneous projected type;
the bare-owner/missing-field fallback needs a compiler root fix. Native field
resolution must retain module-qualified owner identity and reject absent
fields rather than projecting field zero. A precise internal patch and a
native two-module same-name regression remain pending.

Workaround: rename only the guarded selector owner to `CollectionSelectionFacts`
and update its constructors, signatures, imports, exports and tests. Keep the
effects-bearing `CollectionPlanFacts` and extractor unchanged. No compatibility
alias for the old selector name is retained because it would restore ambiguity.
Field order, field types and selector/explanation behavior remain unchanged.

Receipt counts: owners 1-19 passed 48 modules each (912); owner20 claimed48,
passed0, sealed_failed48, exit1. The later wrapper exit89 is a separate
RSS observer measurement failure on PID325 (`ps`), not the native root cause.
Historical SCV snapshot paths and all failed receipts remain preserved.

Validation of this source workaround does not qualify P3 or prove the
compiler owner-resolution bug fixed. No cache deletion or P2 rebuild is needed.

Narrow retained-seed validation (2026-10-26): canonical transcribed interpreter
run of `test/01_unit/compiler/mir_opt/collection_plan_explain_spec.spl` passed
7/7, exit0, quiescent1, enforced 3 GiB tree cap, peak RSS 379472 KiB.
Inputs before/after matched. Evidence is retained under the review workspace
`build/verify/collection-selection-owner-regression-20261026-01/`.
The new scalar counter case covers admitted positive values, admitted unknown
sentinels and unadmitted positive values. This narrow interpreter test does not
reproduce the full native owner collision; P3 qualification remains required.
Astra reviewed the exact nominal rename and regression before admission.
