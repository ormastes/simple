# Simple traceability, SDN evidence, admission and Slop requirements

Status: selected baseline from the user-supplied final report and explicit full implementation request. No implementation or execution claim.

Source: [final report](../../09_report/simple_traceability_sdn_slop_final_2026-10-03.md). Date: 2026-10-03. Research baseline: 88ecaa21054aea80eb7c8dd46052c344837fe78a.

| ID | Requirement |
|---|---|
| REQ-TRC-001 | All Simple-owned structured traceability interfaces and storage shall use schema-versioned SDN. |
| REQ-TRC-002 | Every enforced feature shall resolve to requirements and acceptance criteria without relying on prose substring matching as proof. |
| REQ-TRC-003 | The graph shall distinguish acceptance, unit, integration, and component test definitions and their actual executions. |
| REQ-TRC-004 | Deterministic conventional links shall not require redundant authored DB rows. |
| REQ-TRC-005 | Irregular and many-to-many relationships shall support explicit, attributable declarations. |
| REQ-TRC-006 | Conflicting or ambiguous relationships shall not be silently resolved by choosing the first match. |
| REQ-TRC-007 | Every diagnostic shall identify its snapshot, rule, affected entity, and evidence/provenance. |
| REQ-TRC-008 | Local commit validation shall inspect the staged snapshot or the equivalent SJ-frozen candidate, not unstaged file bytes. |
| REQ-TRC-009 | Push validation shall cover every relevant proposed ref update and handle creation, deletion, and non-fast-forward cases explicitly. |
| REQ-TRC-010 | Admission shall be bounded, offline locally, read-only with respect to tracked source, and fail explicitly when required scope cannot be checked. |
| REQ-TRC-011 | Remote admission shall use trusted checker code/policy and validate the exact candidate subject. |
| REQ-TRC-012 | Feature-level test execution shall always emit a traceability SDN artifact and a Markdown run report, including failures and partial runs. |
| REQ-TRC-013 | A requirement shall not receive verified coverage from a merely linked, skipped, missing, stale, or unexecuted test. |
| REQ-TRC-014 | Generated structural documents shall be deterministic and separate from mutable “latest run” pointers. |
| REQ-TRC-015 | Slop shall expose tree navigation, a layered graph, and a detail/source inspector over the same graph as CLI and documentation. |
| REQ-TRC-016 | Feature, layer, component/entity, and transform dimensions shall coexist without duplicating canonical artifacts or weakening MDSOC boundaries. |
| REQ-TRC-017 | The incremental result shall match a full rebuild for the same complete input snapshot and rule versions. |
| REQ-TRC-018 | Existing feature/test DB data shall migrate without silent link loss, duplicate writers, or invalidating historical evidence by relabeling it. |
| REQ-TRC-019 | Exceptions and baseline debt shall be scoped, reviewable, expiring where applicable, and unable to turn unknown evidence into pass. |
| REQ-TRC-020 | Static HTML and Slop shall retain revision, provenance, visibility, and source-navigation semantics without requiring a JSON service. |

Additional development acceptance: retain complete requirement-to-scenario-to-implementation-to-run-to-review/delivery provenance for this feature itself; see the acceptance plan. Existing REQ-TRC identifiers and all report scope are preserved. No automatic done transition, JSON fallback, seed verification, or replacement data owner is permitted.
