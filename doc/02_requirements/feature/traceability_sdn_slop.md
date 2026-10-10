# Traceability, SDN evidence, admission, and Slop requirements

Status: selected implementation baseline; execution qualification pending.
Authority: [final report](../../09_report/simple_traceability_sdn_slop_final_2026-10-03.md), sections 4, 18, 21–23.
Selection: the user's instruction to implement the referenced report with
`spipe:dev`, Astra review, TDD, and modern SSpec acceptance tests. This records
that selected scope; it introduces no replacement option or narrower MVP.

| ID | Required behavior |
|---|---|
| REQ-TRC-001 | All Simple-owned structured traceability interfaces and storage use schema-versioned SDN. |
| REQ-TRC-002 | Enforced features resolve to requirements and acceptance criteria through declarations, never prose substring proof. |
| REQ-TRC-003 | Acceptance, unit, integration, and component definitions and actual executions remain distinct. |
| REQ-TRC-004 | Deterministic conventional links need no redundant authored DB rows. |
| REQ-TRC-005 | Irregular and many-to-many links have explicit attributable declarations. |
| REQ-TRC-006 | Conflicting and ambiguous links fail resolution rather than picking the first candidate. |
| REQ-TRC-007 | Diagnostics identify snapshot, rule, entity, and provenance. |
| REQ-TRC-008 | Commit validation inspects the exact index or SJ-frozen candidate. |
| REQ-TRC-009 | Push validation checks every proposed ref, with explicit create/delete/non-fast-forward semantics. |
| REQ-TRC-010 | Admission is bounded, offline locally, read-only for tracked source, and explicitly incomplete when scope cannot be evaluated. |
| REQ-TRC-011 | Remote admission uses independently trusted code/policy and validates the exact candidate. |
| REQ-TRC-012 | Every feature run emits SDN and Markdown, including failed and partial runs. |
| REQ-TRC-013 | Linked, skipped, missing, stale, and unexecuted tests cannot confer verified coverage. |
| REQ-TRC-014 | Structural documents are deterministic and separate from mutable latest-run pointers. |
| REQ-TRC-015 | Slop offers tree, layered graph, and details/source inspection over the shared graph. |
| REQ-TRC-016 | Feature, layer, component/entity, and transform dimensions share canonical artifact identities and preserve MDSOC boundaries. |
| REQ-TRC-017 | Incremental and full results agree for identical complete inputs and rule versions. |
| REQ-TRC-018 | DB migration preserves links, one writer, and historical evidence validity. |
| REQ-TRC-019 | Debt and exceptions are scoped/reviewable/expiring as applicable and cannot turn unknown evidence into pass. |
| REQ-TRC-020 | HTML and Slop preserve revision, provenance, visibility, and navigation semantics without a JSON service. |

The acceptance authority is the report's complete AC-TRC-001 through
AC-TRC-040 matrix, mapped in [the test plan](../../03_plan/sys_test/traceability_sdn_slop.md).
User-requested delivery constraints: Astra reviews plan/design and final changes;
tests precede their implementation; modern SSpec uses real assertions and manual
steps. No requirement is complete from a declaration, synthetic fixture, stale
binary, or unexecuted test. WP7 extends views using the same graph; optional
external publication requires its own authorized integration action.
