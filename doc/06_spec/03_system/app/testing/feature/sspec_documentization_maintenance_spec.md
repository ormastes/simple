# SSpec Documentization Maintenance

## Purpose and audience

This operator specification is for SSpec authors, maintainers, reviewers, and
LLM agents. It explains how to interpret documentization quality, preview safe
maintenance, preserve reference provenance, and review the resulting SPipe
manual without confusing scaffolding with conformance evidence.

## Scope and preconditions

The executable system scenarios exercise the pure, in-memory maintenance
owners. CLI exit codes, directory traversal, JSON/SARIF stdout purity, atomic
file replacement, permission preservation, and rollback files remain covered
by focused integration tests. This manual does not claim those behaviors from
source inspection.

Use the self-hosted Simple toolchain. Executable `.spl` stays under `test/`;
this mirrored `doc/06_spec/` artifact is Markdown only.

## Operator workflow

1. Inspect the SSpec documentization baseline.
2. Review scored improvement findings and blockers.
3. Preview safe mechanical changes without changing source.
4. Confirm only the exact reviewed maintenance changes.
5. Scaffold traceable scenarios from a reference specification.
6. Compare active findings with the reviewed baseline.
7. Generate and inspect the professional specification manual.

## Scenario narratives

### Score every professional documentization dimension

The analyzer reports narrative, structure, oracle quality, traceability,
evidence, coverage, and maintainability independently. The scenario asserts all
seven typed values and the aggregate; it does not infer quality from one pass
marker.

### Expose blockers instead of averaging them away

A fixture with executable structure but no expectation produces
`SSDOC-ORA-001`; missing requirement identity produces `SSDOC-TRC-001`. At
least one blocker is present and the aggregate remains below 50.

### Preview and confirm safe maintenance

Preview returns proposed content plus the original rollback content while the
input bytes remain unchanged. Applying the supported transformation yields the
same reviewed content, and applying it again reports no change.

This proves the in-memory transformation contract. Filesystem atomicity,
permission preservation, conflict detection, and retained rollback paths are
separate integration obligations.

### Scaffold traceable, fail-fast SSpec

Reference intake preserves the reference path, exact SHA-256, and `REQ-001`.
It retains source line 2, the explicit normative statement as an `Expected`
comment, a source-to-scenario mapping row, a visible
`step("Review unresolved action for REQ-001")`, and an executable failing TODO.
It emits no `expect(...)` from prose.
The scaffold is therefore reviewable provenance, never a false passing test.

### Compare stable finding identity

The baseline helper classifies a retained fingerprint as `unchanged`, a new
fingerprint as `new`, and a missing prior fingerprint as resolved. The CLI
accepts the reviewed fingerprint ledger with `--baseline` and reviewed
`RULE_ID|owner|reason|optional-fingerprint` records with `--suppressions`.

### Render the maintenance appendix for the professional manual

The composition scenario starts from a SPipe-owned professional body and checks
that the authored body remains the exact prefix, then checks purpose/audience,
primary workflow, deterministic generation history, source identity, the
scorecard, current mirror state, and absence of invented TODO prose. Maintenance supplies
observed provenance and scoring without duplicating SPipe's scenario renderer.

## Scorecard interpretation

| Dimension | Weight | Meaning |
|---|---:|---|
| Narrative | 15% | Purpose, audience, and authored context |
| Structure | 15% | Readable hierarchy and ordered behavior |
| Oracle | 20% | Production-observing, non-tautological assertions |
| Traceability | 15% | Stable requirement-to-scenario bindings |
| Evidence | 15% | Visible actions, outcomes, captures, and environment |
| Coverage | 10% | Boundaries, failures, recovery, and unsupported states |
| Maintainability | 10% | Helpers, folding, compatibility, and limitations |

Any blocker caps the aggregate at 49. Review each component and finding rather
than treating the weighted total as the sole acceptance decision.

## Requirements and test traceability

| Requirement | Executable scenario | Evidence |
|---|---|---|
| REQ-SSDOC-002/003/004 | score dimensions; blocker findings | typed scores and stable rule IDs |
| REQ-SSDOC-006/012 | baseline identity | exact `new`, `unchanged`, and resolved values |
| REQ-SSDOC-007 | preview/apply/idempotence | exact source, rollback, and transformed content |
| REQ-SSDOC-008 | reference scaffold | path, SHA-256, REQ ID, step, failing TODO |
| REQ-SSDOC-009/011 | professional manual composition | authored sections, generation history, scorecard, and current source identity |

## NFR traceability and open evidence

| NFR | Evidence in this manual/lane | Status boundary |
|---|---|---|
| NFR-SSDOC-008 | scaffold never emits a passing oracle; LLM policy is preview-only | Core operations are offline; no network/LLM behavior is claimed by this in-memory spec |
| NFR-SSDOC-011 | stderr-only scan parse/mirror/rule/render/cache timing and improve preview/conflict/reparse/write timing | Timing output remains operational evidence and never contaminates machine report stdout |
| NFR-SSDOC-012 | executable scenarios, this operator manual, score dimensions, and REQ mapping | >=80% branch evidence and zero-stub docgen remain focused verification gates |

REQ-SSDOC-001/005/010 and filesystem portions of REQ-SSDOC-007/012 are not
claimed by these library scenarios; focused unit/integration tests own the
command/MCP surfaces, JSON/SARIF, policy exits, directory and cache behavior,
suppression records, atomic mode-preserving apply, rollback, and scaffold write
confirmation.

## Findings, recovery, and troubleshooting

- Fix blockers before score improvements.
- If preview changes meaning, decline it and author the correction manually.
- If apply or verification fails, preserve diagnostics and use retained
  rollback material; do not report the edit accepted.
- If reference prose lacks an oracle, keep the generated TODO failing until an
  authoritative expectation is selected.
- If the mirror is missing or stale, regenerate through SPipe and reread it.
- A suppression requires stable rule ID, owner, reason, and bounded scope; it
  cannot hide a blocker or failing scaffold.

## Evidence and provenance

- Executable source:
  `test/03_system/app/testing/feature/sspec_documentization_maintenance_spec.spl`
- Requirements:
  `doc/02_requirements/feature/sspec_documentization_maintenance.md`
- System-test plan:
  `doc/03_plan/sys_test/sspec_documentization_maintenance.md`
- Architecture:
  `doc/04_architecture/sspec_documentization_maintenance.md`
- Detail design:
  `doc/05_design/sspec_documentization_maintenance.md`
- Operator guide:
  `doc/07_guide/infra/sspec_documentization_maintenance.md`

The current source hash is recorded by the canonical generator/maintenance
output during verification. Do not hand-copy a stale hash into this manual.

## Compatibility and limitations

`simple spipe-docgen` remains compatible and canonical for full scenario
manuals. Optional LLM suggestions are source-evidenced previews, excluded from
deterministic scoring, never self-approved, and never self-applied. Reviewed
suppression records require rule, owner, reason, and optional fingerprint;
blockers cannot be suppressed. Filesystem conflict, rollback, and
permission-preservation evidence remains owned by focused integration tests.
Full external-standard ingestion is planned under canonical `spec-to-spipe`;
`spec-to-sspec` is the compatibility name that must route to the same semantic
pipeline when its production command lands. The current Phase 0 contracts are
not a production CLI. The bounded Markdown scaffold does not claim lossless
byte coverage or official conformance bindings.

<details><summary>Executable SSpec</summary>

The canonical executable is linked above. No second `.spl` copy is stored under
`doc/06_spec`.

</details>
