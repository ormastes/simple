# SMF Manifest Current-version Gate

- Executable: `test/01_unit/compiler/driver/smf_manifest_gate_spec.spl`
- Requirements: `KPM-NFR-005`, `KPM-REQ-004`, `KPM-REQ-006`, `KPM-REQ-009`
- Evidence class: executable SPipe definition; no execution summary is embedded.

## Scenarios
- admits the production writer serialize parse path.
- rejects legacy version 34 with a named version code.
- rejects an unknown version rather than defaulting it.
- rejects an ABI mismatch with a named code.
- admits a matching current-version ABI digest.
- round-trips identity columns.
- serializes entries and interface sets canonically.
- rejects malformed and duplicate rows instead of dropping them.

## Selected Policy
- ABI epoch is v1. Checked parsing rejects legacy or unknown schema versions
  before source lookup or cache admission.

## Freshness
- Requirement IDs and scenario names mirror the executable source as of 2026-09-02.
- The executable contains no `pass_todo` or tautological `expect(true).to_equal(true)` evidence.
- Runtime execution was not available in this audit because the admitted self-hosted `bin/simple` lacks `test`; no runtime PASS is claimed.
