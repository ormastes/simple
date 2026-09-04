# MacOS M5 Universal Packaging Integration

- Executable: `test/02_integration/bootstrap/macos_universal_m5_spec.spl`
- Requirements: `MBH-NFR-004`, `MBH-NFR-005`, `MBH-REQ-007`
- Evidence class: executable SPipe definition; no execution summary is embedded.

## Scenarios
- rejects invalid slices, stale evidence, mutation, and rebuild promotion.

## Selected Policy
- Universal promotion requires retained arm64 and x86_64 M4 receipts plus real Apple signing/notary evidence.

## Freshness
- Requirement IDs and scenario names mirror the executable source as of 2026-09-02.
- The executable contains no `pass_todo` or tautological `expect(true).to_equal(true)` evidence.
- Runtime execution was not available in this audit because the admitted self-hosted `bin/simple` lacks `test`; no runtime PASS is claimed.
