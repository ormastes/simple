# Versioned SFFI Real Plugin Entry Negotiation

- Executable: `test/01_unit/lib/sffi/dynamic_versioned_negotiate_spec.spl`
- Requirements: `KPM-NFR-003`, `KPM-NFR-005`, `KPM-REQ-004`, `KPM-REQ-006`, `KPM-REQ-009`, `KPM-REQ-011`
- Evidence class: executable SPipe definition; no execution summary is embedded.

## Scenarios
- returns a handle only after accepting the full older descriptor.
- does not let a malformed host reuse a previously negotiated handle.
- returns no handle for a different major.
- accepts an older compatible minor.
- returns no handle when any full digest byte differs.
- refuses a missing capability before cache publication.
- refuses a different concrete Simple ABI before cache publication.
- returns no handle for a corrupt descriptor.
- closes the provider on every pre-publication refusal branch.

## Selected Policy
- This scenario has no additional user-selected policy beyond its listed requirements.

## Freshness
- Requirement IDs and scenario names mirror the executable source as of 2026-09-02.
- The executable contains no `pass_todo` or tautological `expect(true).to_equal(true)` evidence.
- Runtime execution was not available in this audit because the admitted self-hosted `bin/simple` lacks `test`; no runtime PASS is claimed.
