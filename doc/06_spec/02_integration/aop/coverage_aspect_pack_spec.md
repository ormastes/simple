# Coverage And Logging Aspect Packs

- Executable: `test/02_integration/aop/coverage_aspect_pack_spec.spl`
- Requirements: `KPM-NFR-001`, `KPM-NFR-002`, `KPM-NFR-004`, `KPM-NFR-006`, `KPM-REQ-005`, `KPM-REQ-008`, `KPM-REQ-009`, `KPM-REQ-013`
- Evidence class: executable SPipe definition; no execution summary is embedded.

## Scenarios
- uses static bootstrap activation and startup/lazy test activation.
- keeps activation semantics explicit while selecting atomic APK-only coverage.
- wires the selected atomic APK-only state at the production coverage boundary.
- registers and activates a resident production STARTUP binding.

## Selected Policy
- Coverage cutover: atomic APK-only; legacy rewriting is not qualifying evidence.

## Freshness
- Requirement IDs and scenario names mirror the executable source as of 2026-09-02.
- The executable contains no `pass_todo` or tautological `expect(true).to_equal(true)` evidence.
- Runtime execution was not available in this audit because the admitted self-hosted `bin/simple` lacks `test`; no runtime PASS is claimed.
