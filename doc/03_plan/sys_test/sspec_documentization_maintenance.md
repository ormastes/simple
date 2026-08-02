# SSpec Documentization Maintenance — System Test Plan

## Scope and traceability

The acceptance suite covers `REQ-001` through `REQ-012` and `NFR-001` through
`NFR-012` from the selected requirements. Unit tests own rule witnesses,
scoring, rendering, cache invalidation, fix conflicts, scaffold mapping, and
mirror derivation. Integration tests own CLI exit codes and machine-output
purity. The system specification owns the operator flow and generated manual.

## Fixed operator flow

1. Inspect the SSpec documentization baseline.
2. Review scored improvement findings.
3. Preview safe mechanical changes.
4. Confirm selected maintenance changes.
5. Generate and inspect the professional specification manual.

The executable scenario uses literal `step("...")` calls so SPipe docgen can
extract them. Helpers that are not implemented must call
`fail("TODO: replace generated placeholder with an executable assertion")`.

## Test inventory

- Unit: analyzer/rules, score, renderers, improvements, scaffold, cache, mirror.
- Integration: `simple sspec-maintain` help, operations, formats, gates, and
  preview/apply behavior.
- System: professional scoring, safe improvement, reference scaffolding,
  complete manual generation, compatibility/workflow inventory.
- Performance: warm single-pair p95 and deterministic 1,000-pair corpus.

Fixtures live under `test/fixtures/sspec_documentization_maintenance/` and use
`.txt` for generated SSpec goldens so test discovery cannot execute them.

## Required evidence

Assertions compare exact rule IDs, dimensions, scores, exit codes, fingerprints,
paths, byte strings, and parsed JSON/SARIF fields. Preview and declined fixes
leave bytes unchanged; apply preserves permissions, writes rollback material,
rejects overlap/staleness, reparses, and is idempotent. The scaffold records the
reference hash and emits visible fail-fast placeholders for unresolved facts.

The generated manual must contain Purpose and audience, Preconditions,
Operator workflow, Scenario narratives, Scorecard, Findings and remediation,
Evidence and provenance, and Compatibility and limitations. Native acceptance
uses the self-hosted runtime with stub fallback disabled.

## Performance and stop rule

Measure in-process warm p95 excluding startup, total time and maximum RSS for a
1,000-pair manifest, cache hit/miss counts, and phase timings. Run each gate once
per verification session and stop after convergence.
