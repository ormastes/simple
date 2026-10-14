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
