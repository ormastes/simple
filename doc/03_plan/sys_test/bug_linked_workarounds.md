# Test plan: bug-linked workarounds

| Requirement | Scenario |
|---|---|
| REQ-001 | Parse minimal/complete `#` and `//` annotations; reject missing/invalid bug IDs and invalid recovery hashes. |
| REQ-002 | Round-trip textual records; join the canonical bug database; diagnose orphan bug IDs. |
| REQ-003 | Add/change/remove links through incremental updates; delete and revert annotated files; reconcile a fullscan. |
| REQ-004 | Show open links and resolved recovery warnings from a prebuilt index; filter by bug ID; prove query has no source discovery. |
| REQ-005 | Missing/stale index requests fullscan; malformed batch and lock failures preserve previous valid bytes. |
| REQ-006 | Recovery metadata renders as review guidance, never a destructive command; verify build does not clear unrelated cache entries. |
| REQ-007 | Operator examples agree with parser/CLI; skill/wiki links resolve. |

Executable system spec belongs under
`test/03_system/app/bug/feature/bug_linked_workarounds_spec.spl` and its manual
under the mirrored `doc/06_spec/03_system/app/bug/feature/` directory.
Unit/integration fixtures cover parsing and persistence boundaries. Do not
claim that structural tests establish compiled runtime or performance results.
Record actual runtime, command, result counts, and unresolved execution gaps.

NFR checks review the query/build call graph, verify facade ownership, and
measure warm fixture query latency. Use existing self-hosted artifacts and
compatible caches. Focused tests do not require a full bootstrap rebuild.
