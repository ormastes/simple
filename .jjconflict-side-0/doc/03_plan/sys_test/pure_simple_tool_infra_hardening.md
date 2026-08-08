<!-- codex-design -->
# Pure-Simple tool infrastructure system-test plan

Executable scenario:
`test/03_system/app/tooling/feature/pure_simple_tool_infra_hardening_spec.spl`.

| Scenario | Requirement coverage | Evidence |
|---|---|---|
| Admit truthful runtime/inventory | REQ-001, REQ-002, REQ-011; NFR-003, NFR-011, NFR-012 | bounded candidate provenance, rollback, table-derived dispatch |
| Preserve developer-tool failures | REQ-003–REQ-006, REQ-009, REQ-010, REQ-014; NFR-002, NFR-004 | child exits, structured counts, qualification placeholder scan, lint/fix JSON and atomic source contracts |
| Gate fresh essential tools | REQ-003, REQ-007, REQ-009, REQ-010; NFR-004 | real/red/empty/forged runner matrix, lint clean/deny, duplication clean/found |
| Reject unsafe/stale paths | REQ-007, REQ-008, REQ-012, REQ-013; NFR-001, NFR-008, NFR-010, NFR-012 | hostile paths, native-first wrappers, cache invalidation, daemon lifecycle |
| Retain measurable evidence | REQ-015; NFR-005–NFR-009 | every child call bounded to 30s, p95/RSS/hash evidence |

Run source contracts first. After a fresh Stage 4 is admitted, run each focused
acceptance probe once, then generate the manual with zero stubs. Do not repeat
green acceptance checks.
