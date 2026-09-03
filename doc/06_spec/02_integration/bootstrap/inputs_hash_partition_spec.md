# Bootstrap Kernel Input Partition

- Executable: `test/02_integration/bootstrap/inputs_hash_partition_spec.spl`
- Requirements: `KPM-NFR-004`, `KPM-NFR-006`, `KPM-REQ-001`, `KPM-REQ-008`, `KPM-REQ-009`
- Evidence class: executable SPipe definition; no execution summary is embedded.

## Scenarios
- uses the fail-closed authoritative closure stream.
- has a mutation-red host-independent partition checker.

## Selected Policy
- This scenario has no additional user-selected policy beyond its listed requirements.

## Freshness
- Requirement IDs and scenario names mirror the executable source as of 2026-09-02.
- The executable contains no `pass_todo` or tautological `expect(true).to_equal(true)` evidence.
- Runtime execution was not available in this audit because the admitted self-hosted `bin/simple` lacks `test`; no runtime PASS is claimed.
