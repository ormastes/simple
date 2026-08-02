# SSpec Documentization Maintenance

## Purpose and audience

For SSpec authors, maintainers, reviewers, and LLM agents improving executable
specifications with deterministic evidence.

## Preconditions

Use the self-hosted Simple toolchain; keep executable `.spl` under `test/` and
manual Markdown under `doc/06_spec/`.

## Operator workflow

1. Inspect the SSpec documentization baseline.
2. Review scored improvement findings.
3. Preview safe mechanical changes.
4. Confirm selected maintenance changes.
5. Generate and inspect the professional specification manual.

## Scenario narratives

The executable system spec covers explainable scoring, preview/apply
idempotence, traceable fail-fast scaffolding, and complete manual sections.

## Scorecard

The dimensions are narrative, structure, oracle quality, traceability, evidence,
coverage, and maintainability. Blockers cap the effective aggregate at 49.

## Findings and remediation

`SSDOC-*` findings provide dimension, evidence, rationale, remediation,
confidence, fingerprint, and fixability. `SPIPE001..007` retain their identities.

## Evidence and provenance

- Executable: `test/03_system/app/testing/feature/sspec_documentization_maintenance_spec.spl`
- Source SHA-256: `db582bdcbb35b30df519bc28c8ed8d670842456296d372991c6e8cd659a49a79`
- Requirements: `doc/02_requirements/feature/sspec_documentization_maintenance.md`
- Architecture: `doc/04_architecture/sspec_documentization_maintenance.md`
- Design: `doc/05_design/sspec_documentization_maintenance.md`

## Compatibility and limitations

SPipe remains the complete-manual generator. LLM suggestions are optional,
preview-only, excluded from scores, and never self-applied.

<details><summary>Executable SSpec</summary>

See the executable source above; this review artifact links it without creating
a second executable copy under `doc/06_spec`.

</details>
