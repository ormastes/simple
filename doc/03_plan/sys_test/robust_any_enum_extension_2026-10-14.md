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
