# Robust Any warnings and return-operand enum extension prevention

User-selected scope: warn about Any uses under robust; prevent enum extension bugs.

REQ-001: robust/critical lint profiles default written_any_decl,
any_fallback_use, and any_receiver_use to warn. Moderate/strict remain allow;
explicit overrides and the environment off switch remain authoritative.
Existing any_warn_rules_acceptance_spec.spl checks profile descriptors and
real lowered-HIR findings, clean concrete types, enum names, comments, and strings.

REQ-002: return operand projections classify Copy, Move and Const explicitly.
return_operand_enum_extension_spec.spl checks their values and absent returns.
Existing critical_wildcard_coverage_spec.spl checks injected enum variants.
Outer non-return terminator fallbacks remain intentional; no universal enum audit is claimed.

Verification: execution UNRUN. The available pure producer is bootstrap-only;
it cannot run the full lint/spec CLI, and paired native collector fixtures fail
with E-MONO-032 for _function_field_enum_discriminant<T>. Source review and
whitespace/environment guards are separate from executable test evidence.

Performance limitation: enabling HIR-backed warnings invokes a check child.
The existing guide recorded 23.5s to 59.0s historical file lint latency;
this requested default change does not repair that performance debt.
The active Phase3 build uses a frozen prior source snapshot and does not test
these new warning/enum changes.

## 2026-10-19 selected follow-up: enum hardening and coverage

The user requested an additional agent to harden enum extension, the hardening
feature, and coverage. This appendix refines that selected scope; it does not
change REQ-001 or claim a general enum implementation is complete.

REQ-002 now has independent Copy and Move tag/ID oracles, all nine
`MirConstValue` variants (including both floating representations), absent
returns, and intentional non-return terminator sentinels. An inlined real
frontend/HIR/MIR regression adds `Borrow(i64)` to a Copy/Move/Const enum while
leaving its classifier unchanged. It requires the missing-variant diagnostic
and a divergent panic/Abort path; the original enum is the negative control.
Outside critical this path remains warning plus runtime trap, not a promised
compile-time rejection. Run that scenario under robust during qualification.
The existing critical wildcard specification checks coverage objects; complete
compiler wiring for critical wildcard rejection remains separately unqualified.

REQ-ENUM-FRAME-OWNER: project a present optional frame before matching the
`HirChildFrame` owner or forwarding it to child expansion. The concrete defect
is `CollectionRegionCollectorV1.scan` matching `work.pop()` directly, although
pop returns an optional. The collector owns this stack exclusively; its
nonempty check and pop have no intervening mutation. Explicit typed unwrap
preserves that invariant without a fabricated frame or relaxed payload rule.
Traversal order, pruning, and complexity remain unchanged by construction;
no measured performance or memory claim follows from this source argument.

| Requirement / boundary | Executable oracle | Status |
|---|---|---|
| REQ-002 current projections | `test/01_unit/compiler/mir/return_operand_enum_extension_spec.spl` | Authored, UNRUN |
| REQ-002 injected variant | `test/01_unit/compiler/mir/enum_match_fallthrough_trap_spec.spl` | Authored, UNRUN |
| REQ-ENUM-FRAME-OWNER traversal | `test/01_unit/compiler/semantics/collection_plan_extractor_spec.spl` | Source repair and sibling-order/leaf-drain regressions authored, UNRUN |
| REQ-ENUM-FRAME-OWNER projection and negative contracts | `test/01_unit/compiler/mir/optional_enum_payload_owner_spec.spl` | Optional-field unwrap positive, unprojected optional negative, foreign-owner negative; UNRUN |
| Existing critical wildcard/injected coverage objects | `test/01_unit/compiler/hir/exhaustiveness/critical_wildcard_coverage_spec.spl` | Existing, runtime qualification outstanding |

Remaining historical audit matrix (group numbers are identifiers, not current
failure counts):

| Groups | Boundary / remaining evidence |
|---|---|
| 107 | Concrete Option/frame owner repair authored here; current producer execution still required |
| 108 | Two constructor diagnostics are not uniquely attributed; this change does not establish their repair |
| 35, 36, 38 | PassScope projection/ambiguous bare patterns belong to the independent source audit; unchanged here |
| 99 | Lowercase enum-pattern resolution; unchanged here, admission source excluded |
| 104, 111, 116, 117, 120 | Result unwrap/unwrap_err receiver payloads require exact evidence; unchanged here |
| 155 | Merged Some/nil payload typing; unchanged here |

The earlier 40-group audit's 28 source-covered / 12 open classification is
historical evidence, not a current completion count. Neither group 107 nor any
other group is marked runtime-closed by this authoring pass.

Implementation author: isolated enum-hardening agent. Merge owner and final
qualification: root. Independent exact-head reviewer: Astra assigned by root.
Additional sidecars: N/A for this bounded repair. No compiler, native build,
spec runner, or doc generator was launched by the author. Existing three build
attempts remain consumed; root controls the user-authorized six-attempt cap.
Source/whitespace review is separate from runtime, formal, and performance
qualification. The mandatory compiler/lib/MCP checks and focused regressions
remain pending with root; no STATUS: PASS or release qualification is claimed.

## 2026-10-19 PassScope follow-up

REQ-ENUM-PASS-SCOPE: retain the declared descriptor and enum subject across
optional unwrap/field projection in the two checked pass dispatch functions.
Port the donor's typed `MirPassDescriptor`, typed `PassScope` local, and fully
qualified Module/Function/FsDriver arms. Preserve all status and structural
guards, unknown/no-op contracts, and module iteration ordering.

Source scope is only `src/compiler/60.mir_opt/mir_opt/mod.spl`, functions
`run_named_pass_with_record` and `run_pass_on_module_checked`. The dedicated
`test/01_unit/compiler/mir_opt/pass_scope_enum_owner_spec.spl` and its mirrored
authored manual exercise real registry lookup, alias identity, active Module
dispatch boundaries, inactive Function/FsDriver skips, unknown requests, and
malformed-input rejection. Tests were authored before the production edits.

Historical groups 35/36/38 now have an authored source mitigation, pending
independent review and actual compiler evidence. They are not runtime-closed.
All other prior matrix rows retain their boundaries. Active Function/FsDriver
branches are unreachable under current pass statuses and remain uncovered;
the patch does not enable them. Exact stale adjacent test cases are tracked in
`doc/08_tracking/bug/pass_scope_enum_owner_projection_2026_10_19.md`.

Additional sidecars: N/A. Root owns independent exact-head review and runtime
qualification. No compiler, tests, native builds, or doc generation were
launched for this port; the existing six-total attempt accounting is unchanged.

## 2026-10-19 remaining coherence payload follow-up

Base `7ac25381e98545e7ad57503428094d1b1e3811ba` contains collector PR 3762 and
PassScope PR 3765. Their source fixes are retained; their presence alone does
not discharge runtime qualification or the remaining historical audit groups.

REQ-ENUM-COHERENCE-PAYLOAD: preserve `Some(text)`/nil suggestion metadata at
`CoherenceError.OrphanImpl`, exact diagnostic payload ordering and ownership,
and fail-closed behavior for unknown variants/unsupported payload kinds.
The selected repair annotates the suggestion `text?` and qualifies the four
diagnostic variants. It preserves the O(1) local-type presence query, existing
orphan rules, and exact strings. No fallback/default enum behavior is added.

| Boundary | Executable regression | Evidence |
|---|---|---|
| Optional suggestion, local/foreign rules, four diagnostic variants | `test/01_unit/compiler/traits/trait_coherence_optional_payload_spec.spl` | Seven scenarios authored; UNRUN |
| Typed optional text merge / wrong optional primitive rejection | `test/01_unit/compiler/mir/optional_enum_payload_owner_spec.spl` | Two added scenarios; UNRUN |
| Unsupported payload kind, unknown variant, wrong arity | `test/01_unit/compiler/mir/enum_payload_extension_boundary_spec.spl` | Two scenarios through production boundary methods; UNRUN |
| Registry nonmutation with 128 local types | Coherence spec above | Behavioral oracle only; no time/RSS/allocation measurement |

Historical group 155 gains a consumer source mitigation, not a general
branch-join inference repair or runtime closure. Groups 99/104/108/111/116/117/120
remain unresolved; no result-payload support was widened without exact
receiver evidence. The tracking record is
`doc/08_tracking/bug/coherence_optional_payload_owner_2026_10_19.md`.

Author: dedicated isolated enum agent. Independent review: Astra peer assigned
by root. Merge/runtime owner: root. Additional sidecars: N/A. Use the existing
SSpec/native test workflow from
`doc/07_guide/infra/testing/native_test_binary_workflow.md`; no new test toolchain
or runner is introduced. Compiler/native execution, formal and performance
qualification remain UNRUN. No retry budget is reset by this new worktree.

## 2026-10-19 concrete Result dictionary payload repair

REQ-ENUM-RESULT-DICT: support no-default unwrap/unwrap_err for a declared
dictionary Result payload, preserving its handle, key/value types and nominal
ownership; reject unsupported/default-bearing forms, evaluate the receiver
once, and make wrong/unknown Result tags diverge rather than fabricate a value.

The exact source witness is the name-index update in
`ModuleSurfaceBuilder.add_indexed_name`: its helper returns
`Result<Dict<text, i64>, text>` while the unwrap admission switch omitted Dict.
The production fix is confined to `lower_result_unwrap_core` in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`. It reuses the
existing raw dictionary ABI and normal type/provenance bookkeeping. The
no-default panic edge now terminates Abort; supported default paths retain
their merge semantics. No dictionary traversal, cloning, allocation call,
cache policy or test toolchain is added.

Six actual-value scenarios in `result_dictionary_unwrap_runtime_spec.spl`
cover receiver count, both Result payload directions, scalar/text/nominal
dictionary values, empty dictionaries, and the actual module-index API.
Four actual-MIR scenarios in `result_dictionary_unwrap_lowering_spec.spl`
cover independent type/metadata oracles, raw payload copying, exact calls,
tag/mismatch Abort behavior, rejection diagnostics, and scalar-default
compatibility. Mirrored authored manuals exist; all ten scenarios are UNRUN.

Tracking: `doc/08_tracking/bug/result_dictionary_unwrap_payload_2026_10_19.md`.
Historical group 104 gains one exactly typed receiver repair; other receiver
diagnostics in that module and groups 111/116/117/120 are not automatically
closed. Group 108 attribution and prior runtime qualifications remain open.

Author: isolated enum agent at base
`2f7439a9cebafe4fd34bd9743720e01faed2da5b`. Independent source reviewer: Astra
peer assigned by root. Root owns qualification and normal landing. No compiler
or test launch is authorized here; six-total retry accounting is preserved.
Native performance, allocator/RSS behavior, C bootstrap emission and formal
qualification remain UNRUN; source-level call counts do not establish them.

## 2026-10-20 concrete Result Optional payload route

REQ-ENUM-RESULT-OPTIONAL: unwrap/unwrap_err without a default must retain an
admitted Optional carrier, exact Optional/inner nominal owner, and independent
presence semantics. The exact current witness is
`mir_archive_try_production_repository_v1 -> Result<MonoArchiveFinalRepositoryV1?, text>`
and its `production.unwrap()` consumer in `driver_pipeline_lowering.spl`.
The captured base is `23085fbde5b00c64024b059dc85bdaf673756e67`.

The bounded implementation admits Optional inner i64/bool/f64/Text and current
Struct/Class/Enum declarations, copies the raw payload, and records Optional
and runtime-value provenance. Any/inference/error, unknown/non-type owners,
nominal generic arguments, nested/container inner shapes and default-bearing
forms remain rejected. Result tag checks and divergent mismatch paths are
unchanged. No runtime allocation, clone, scan or ABI change is added.

| Boundary | Authored oracle | Status |
|---|---|---|
| Carrier/type/owner preservation, exact tag and mismatch handling, rejected shapes | `result_optional_unwrap_lowering_spec.spl`, five actual-MIR scenarios | UNRUN |
| Some(0), Some(3), None, false/f64/Text, nominal record projection and error payloads | `result_optional_unwrap_runtime_spec.spl`, four value scenarios | UNRUN |
| Wrong Result variant | Two `result_optional_unwrap*_mismatch` native fixtures | UNRUN |
| Dict compatibility | Existing dictionary spec retains Any/default negative controls and exact current diagnostics | UNRUN |

Tracking: `doc/08_tracking/bug/result_optional_unwrap_payload_2026_10_20.md`.
The initial regression specs preceded production edits; later negative/native
controls are recorded as additions, not executed red/green evidence.

### Remaining robust/enum ledger

| Historical groups / feature | Current scope and next boundary |
|---|---|
| 35/36/38, 107, 155 | Prior PassScope, collector and coherence source repairs retained; no reimplementation or new runtime closure claimed |
| 99 | Lowercase enum owner resolution/admission remains outside this repair |
| 104 | Prior typed dictionary receiver repair retained; unidentified receivers remain outside that claim |
| 108 | Collector constructor payload attribution remains open; a disjoint follow-up must establish which HirExpr field/projection loses ownership before editing collector/type-projection owners |
| 116 | One exact Optional repository route gains source support here; the original module-only diagnostic is not universally discharged |
| 111/117/120 | Result/error receiver types remain unattributed; independent source-receipt work in their driver owners must precede any payload expansion |
| Nested Optional/container/default Result payloads | Deliberately not admitted here; require a separate carrier/projection design and tests after this method-owner lane is integrated |
| REQ-001/REQ-002, critical wildcard and injected variants | Landed source/specs retained; runtime, compiler wiring and documented lint performance qualifications remain open |

Author: dedicated isolated enum lane. Review coordinator:
`proof_constraints_review`; merge/qualification owner: root. Additional
sidecars: N/A. The Char MIR packet remains separately frozen. No compiler,
build, test, docgen, or cache operation was launched; historical retry limits
and stopped build profiles are not reset.

## 2026-10-21 critical static coverage production wiring

REQ-002 requires the existing critical static policy to reach production enum
lowering, including defaults that would otherwise hide a newly added variant.
The previous production check sat inside `if not has_default` and used legacy
`is_exhaustive()`. The static policy API/spec alone did not enforce this path.
The existing severity spec's old critical-wildcard-false assertion is updated
to the later selected static policy; the legacy coverage API remains unchanged.

Implementation owns only `match_exhaustiveness.spl`, the enum-match portion of
`switch_operators_calls.spl`, and the dispatch boundary in `expr_dispatch.spl`.
Critical and the normalized mission-critical alias use the canonical static
missing-ID projection. Other profiles retain existing behavior. Explicitly
covering all variants still permits a default. Guarded named arms cover no
static variant. No new annotation grammar or assurance mode is introduced.

The enum path reuses one unguarded-arm coverage collection for its critical
check and existing no-default warning/trap. Qualified declaration metadata is
preferred; an uncontested owner whose runtime name is its bare name may use
bare metadata. Missing qualified metadata is not substituted with a foreign
bare declaration. Existing unresolved-owner diagnostics remain authoritative.
New default diagnostics identify E-COMPLETE-001, the owner and missing variants.
The old no-default critical diagnostic shape and panic/Abort edge remain.

Wildcard/capture-only matches bypass the enum runtime lowering route. Their
existing normalized-arm scan now identifies catchalls; for an actually resolved
Named enum subject, a critical-only static call uses already-obtained metadata.
It neither reevaluates the subject nor emits enum discriminant/payload calls.
The ordinary scalar/guarded/default routing remains in place. Non-enum and
unresolved subjects do not acquire fabricated enum identities.

Coverage buffers are allocated only for no-default or critical matches.
Ordinary enum defaults reuse existing array references without new coverage
buffers. New critical default diagnostics index missing IDs and render in
one declaration-order pass; no per-missing-variant registry traversal is added.
Existing no-default name rendering is preserved. These are source arguments;
allocation, RSS and latency measurements remain UNRUN.

Eight new actual frontend/HIR/MIR scenarios cover injected variants, aliases,
wildcard/capture-only dispatch, subject call count, guarded arms, wrong owners,
ordinary profile controls, non-enum defaults, and no-default panic/Abort.
The severity spec contains twelve cases: ten carried unchanged, one corrected,
and one added. All twenty cases in these two files are **AUTHORED / UNRUN**;
no compiler, native runner, proof checker, docgen, or build was launched.
Run the real-pipeline specification in an isolated test process because it
sets the existing safety-profile environment and restores the exact nullable
value before assertions. This does not authorize a new runner/toolchain.

Historical groups 108/111/117/120 still lack exact diagnostic/receiver
attribution. Groups 35/36/38/104/107/155 have scoped source fixes on the base;
Optional Result payload and nominal declaration identity are already authored
and published in draft PR4019, not recoded here. PR4020 supplies raw observations,
not authenticated Result refinement. Full robust/enum and C7 qualification
remain open. The frozen Char packet overlaps both MIR owners and requires
later semantic composition; this lane does not edit or activate that packet.

Implementation owner: isolated enum agent. Root owns integration; the assigned
independent reviewer reviews this exact packet. Architecture revision 2 was
approved before production changes. The existing compiler-attempt accounting
is unchanged; no runtime or formal PASS is claimed.
