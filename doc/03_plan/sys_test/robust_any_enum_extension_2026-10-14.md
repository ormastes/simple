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
