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

Separate root-fix draft (not admitted to the workaround build): construction
and parameter provenance select the declaration layout through the existing
canonical identity registry; imported field index lookup uses the same fold;
projected field type lookup refuses conflicted bare provenance. A HIR-identified qualified
layout missing the requested field and a conflicted owner lacking a qualified
layout produce fatal diagnostics. Unconflicted legacy bare layouts remain
available. This draft does not change global module normalization or metadata
registration keys. Focused tests cover owner/index consistency, direct and
literal construction, plain/ref/iso parameter provenance, and missing-layout
fail-closed behavior. Bounded retained-seed interpreter validation ran under canonical session/RSS
control (3 GiB, 120 seconds), with no native build. Attempt01 ran all nine
cases: seven passed and both constructor fixtures failed due to an outdated
one-argument IntLit fixture. The fixture now supplies IntLit(73, nil).
Attempt04 ran only those two constructor cases inside the root-fix worktree:
two passed, exit0, quiescent1, peak RSS1265600 KiB, input hashes unchanged.
The seven genuine passing cases from01 were not rerun. This is seven plus two
passing cases across attempts, not a single nine-case green run.

Attempts02/03 are preserved as wrong-source diagnostics, excluded from
qualification: absolute subset paths placed beneath the review worktree
caused test_runner/child_cwd.spl to select that spec's project, despite outer
cwd and SIMPLE_LIB pointing at the root-fix worktree. Attempt04 places its
subset beneath the root-fix worktree and uses a relative spec path. Its direct
constructor case asserts the new helper's presence and exact owner before
checking actual construction. All receipts remain in the review workspace's
build/verify/qualified-struct-field-rootfix-20261026-{01,02,03,04}/ directories.

Construction canonicalization now lives at the shared lower_struct_construct
boundary before field order/types are read, covering direct calls and struct
literals consistently. The earlier wrong-source result does not prove a
nested-mutation defect; no such defect is claimed. Native P3 qualification is
still pending, and this root-fix must remain separate from the frozen
workaround build until exact-patch admission.

A final scoped guard rejects a requested field absent from a registered exact
qualified value layout even when its HIR annotation is unavailable. Attempt05
ran only that new negative case inside the root-fix worktree: one passed,
exit0, quiescent1, peak RSS1265904 KiB under the same enforced3GiB cap.
Unknown-owner legacy fallback remains unchanged. Genuine coverage is seven
passing cases in01, two in04, and one in05, never a single ten-case green run.
All five attempt receipts are retained;02/03 remain excluded wrong-source
diagnostics. Native P3 validation of this exact root-fix is still pending.

## Phase3 isolated backport — 2026-10-26

Adapted merged donor #4875 `de496e321772` onto phase3 `6555a6e033d`.
The donor's constructor argument rename/provenance prelude was absent here;
it is added narrowly alongside the ordinary layout helper. Existing Result Err
owner checks, provider-demand hooks and all strict SOURCE capture/layout code
are preserved. Ordinary unambiguous legacy fallback is not SOURCE authority.
The donor regression file is preserved exactly. Historical donor attempts above
are not recertified for this adaptation: all new-target SSpecs and native P3
execution remain UNRUN. No compiler, cache or toolchain was launched.

Cycle2 closes review findings: conflicted bare value rows and bare fallback rows
are excluded from field-index selection as they already were from owner/type
selection. Exact qualified provenance remains authoritative. The unavailable-
exact-layout negative fixture now actually marks its bare owner conflicted.
Local and composite Struct prepasses register default flags/expressions under
the selected declaration key only when that key's registered field order agrees;
this prevents Child(value=37) / Child() from silently losing its default when
construction selects the qualified layout. Imported-provider registration is a
separate owner change. New real-frontend default and mismatched-order controls
remain UNRUN; no historical donor execution qualifies this adaptation.
