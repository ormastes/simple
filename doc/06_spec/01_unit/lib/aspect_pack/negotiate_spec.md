# Aspect-pack Dynamic Negotiation

- Executable: `test/01_unit/lib/aspect_pack/negotiate_spec.spl`
- Requirements: `KPM-NFR-003`, `KPM-NFR-005`, `KPM-REQ-004`, `KPM-REQ-006`, `KPM-REQ-009`, `KPM-REQ-011`
- Evidence class: executable SPipe definition; no execution summary is embedded.

## Scenarios
- cannot publish when mandatory host negotiation is absent.
- accepts an older digest explicitly listed by the host.
- refuses host-policy replacement after facet publication.
- refuses a different major with PLUG-E-MAJOR.
- mutation-red refuses a load when digest acceptance is skipped.

## Selected Policy
- This scenario has no additional user-selected policy beyond its listed requirements.

## Freshness
- Requirement IDs and scenario names mirror the executable source as of 2026-09-02.
- The executable contains no `pass_todo` or tautological `expect(true).to_equal(true)` evidence.
- Runtime execution was not available in this audit because the admitted self-hosted `bin/simple` lacks `test`; no runtime PASS is claimed.
