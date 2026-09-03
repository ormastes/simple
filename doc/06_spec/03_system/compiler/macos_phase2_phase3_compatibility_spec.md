# MacOS Bootstrap M3 Cross-phase Reuse Evidence

- Executable: `test/03_system/compiler/macos_phase2_phase3_compatibility_spec.spl`
- Requirements: `MBH-REQ-004`, `MBH-REQ-005`, `MBH-REQ-006`, `MBH-REQ-009`
- Evidence class: executable SPipe definition; no execution summary is embedded.

## Scenarios
- should preserve separate writable cache ownership.
- should compare normalized production output receipts.
- should turn a semantic output mutation red.

## Manual Steps
- Invoke the production read-only compatibility gate.
- Invoke the production comparator with permitted volatile fields.
- Change a non-volatile output byte through the production comparator.

## Selected Policy
- This scenario has no additional user-selected policy beyond its listed requirements.

## Freshness
- Requirement IDs and scenario names mirror the executable source as of 2026-09-02.
- The executable contains no `pass_todo` or tautological `expect(true).to_equal(true)` evidence.
- Runtime execution was not available in this audit because the admitted self-hosted `bin/simple` lacks `test`; no runtime PASS is claimed.
