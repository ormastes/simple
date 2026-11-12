# Unit, primitive-API and scheduled-diagnostics requirements

Status: **OPEN.** Baseline: `origin/release/1.0.0` on 2026-11-12.
Authority: [input plan](../../03_plan/release/1.0.0/inputs_2026-11-12/unified_unit_primitive_api_scheduled_diagnostics_plan_2026-11-12.md); lanes: [lane plan](../../03_plan/release/1.0.0/unit_primitive_api_lane_plan_2026-11-12.md).
This register adds stable ids for tracing; it does not narrow the plan. Every row starts OPEN and moves only with current code plus route-specific spec evidence.

## Diagnostic policy (REQ-DPOL)

| Id | Requirement | Plan | Lane | Status |
|---|---|---|---|---|
| REQ-DPOL-001 | `DiagnosticRulePolicy` lives beside DiagnosticV1 with created_on, warn_since, error_not_before, error_since, removal and per-profile overrides; the same edition + policy snapshot yields the same severity on any day | §0.2, §4 | U1 | OPEN |
| REQ-DPOL-002 | `primitive_api` emits exactly one diagnostic per offending (code, symbol, type path, span) on every entry point | §1, §10.2 | U0 | OPEN |
| REQ-DPOL-003 | `primitive_api` reports the exact byte span of the offending type token (not line 1, not the whole line) | §10.2 | U0 | OPEN |
| REQ-DPOL-004 | No diagnostic offers a fix whose replacement leaves the text unchanged; rules without a real edit are help-only | §0.3, §5 | U0 | OPEN |
| REQ-DPOL-005 | DiagnosticV1 carries multiple ranked fixes with confidence and applicability; legacy `fix` aliases the first Safe/Likely fix; JSON stays compatible | §5 | U1 | OPEN |
| REQ-DPOL-006 | check/driver/lint share one dedup sink and one severity decision | §0.4, §9 P0 | U1 | OPEN |
| REQ-DPOL-007 | `--assurance-warning-phase` never silently downgrades security rules; selective per-rule scheduling | §1 | U1 | OPEN |
| REQ-DPOL-008 | `@allow(primitive_api)` exceptions are scoped and need reason/owner (and expiry for critical); expired/unowned exceptions are diagnosed | §4, §10.3 | U1 | OPEN |

## Public-API type checking (REQ-TYPE)

| Id | Requirement | Plan | Lane | Status |
|---|---|---|---|---|
| REQ-TYPE-001 | Public-API primitive checking walks the resolved, effectively-exported type graph (fields, nested type params, aliases, re-exports, `__init__`) | §0.5, §10.1 | U2 | OPEN |
| REQ-TYPE-002 | Enum payloads, generated methods and macro/AOP output are covered | §1, §10.1 | U2 | OPEN |
| REQ-TYPE-003 | Private primitives stay silent; ABI/FFI boundaries are allowed only under explicit boundary policy | §0.5, §8 | U2 | OPEN |
| REQ-TYPE-004 | The traversal is memoized and O(V+E); no extra parse pass and no global source scan | §0.8, §7 | U2 | OPEN |
| REQ-TYPE-005 | P0 library boundaries (byte_cursor, STUN, HKDF/SQLCipher, packed_span, file, NVMe) use typed quantities and overflow-safe bounds (`pos <= len` then `n <= len - pos`) | §2 P0 | U4 | OPEN |
| REQ-TYPE-006 | Library migration classifies primitives (quantity, offset, index, count, id, timestamp, FFI/wire) and never auto-replaces by name | §2 | U4 | OPEN |
| REQ-TYPE-007 | The `_all_same_primitive` blanket exemption is replaced by a scoped, documented pure-math exemption | §4 | U0 → U4 | OPEN (kept in U0: removal would flag stdlib math helpers before U4 migrates them) |

## Units (REQ-UNIT)

| Id | Requirement | Plan | Lane | Status |
|---|---|---|---|---|
| REQ-UNIT-001 | `unit` is the one keyword; `newunit` parses and warns (never rejected during migration) | §0.1, §3, §8 | U3 | OPEN |
| REQ-UNIT-002 | `unit`, `newunit` and `newtype` share one `UnitDecl` AST/HIR lowering | §9 P1 | U3 | OPEN |
| REQ-UNIT-003 | No unit gets generic arithmetic; ops are declared explicitly; illegal unit arithmetic is an error in every profile | §0.7, §8 | U3 | OPEN |
| REQ-UNIT-004 | Dimensions and domains are distinct (ByteCount vs ByteOffset vs Lba, ...) and not interchangeable | §0.6 | U3 | OPEN |
| REQ-UNIT-005 | Unit suffixes are case-distinct (`_Bc` vs `_bc`); collisions are deterministic errors; suffixes are module-private across modules | §10.5 | U3 | OPEN |
| REQ-UNIT-006 | Release unit arithmetic adds zero branches/allocations versus checked raw arithmetic | §7 | U3 | OPEN |
