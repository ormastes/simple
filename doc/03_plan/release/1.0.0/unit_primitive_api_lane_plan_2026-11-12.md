# Unit / primitive-API / scheduled-diagnostics — lane plan (2026-11-12)

Input (authoritative, retained): [unified_unit_primitive_api_scheduled_diagnostics_plan_2026-11-12.md](inputs_2026-11-12/unified_unit_primitive_api_scheduled_diagnostics_plan_2026-11-12.md).
Requirements: [unit_primitive_api_diagnostics.md](../../../02_requirements/compiler/unit_primitive_api_diagnostics.md).
Base branch: `release/1.0.0`. Every lane is TDD (red then green), lands in small PRs, and owns only the files listed for it.

| Lane | Scope | Owned files (exclusive) | Plan refs | REQ rows |
|---|---|---|---|---|
| U0 | primitive_api no-op EasyFix removal, double-invocation dedup, exact span | `90.tools/fix/rules/impl_/lint_primitive_api.spl`, `90.tools/fix/rules/registry.spl`, `90.tools/fix/builtins.spl`, `90.tools/lint/_LintMain/lint_checks.spl` | §0.3, §1, §9 P0, §10.2 | REQ-DPOL-002..004 |
| U1 | `DiagnosticRulePolicy` beside DiagnosticV1; DiagnosticV1 multi-fix (ranked fixes, legacy `fix` alias) | `00.common/diagnostics/diagnostic_v1.spl`, new policy module + SDN | §0.2, §4, §5 | REQ-DPOL-001, -005..008 |
| U2 | `semantic_api` checker wired on the resolved exported type graph | `35.semantics/lint/**` | §0.5, §1, §9 P0, §10.1 | REQ-TYPE-001..004 |
| U3 | `UnitDecl` shared AST/HIR, `newunit` deprecation warning, explicit unit-op table / arithmetic gate | parser/AST/HIR unit decl, unit op table | §0.1, §0.7, §3, §9 P1, §10.4-5 | REQ-UNIT-001..006 |
| U4 | P0 library overflow-safe bounds (byte_cursor, STUN, HKDF, packed_span, file, NVMe) | the listed `src/lib/**` modules | §2 P0, §9 P2 | REQ-TYPE-005..006 |

Ordering (plan §12): U0 and U1 first (diagnostics), U2 next, U3 then U4. `newunit` stays warning-only throughout.
Out of scope for all lanes: escalation dates (owner ratification, plan §12), P3 UI surfaces, P4 enforcement.
