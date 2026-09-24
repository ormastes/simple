# Phase 8 Package Range Locking

- Executable: `test/03_system/app/pkg/feature/requires_range_spec.spl`
- Requirements: `KPM-REQ-009`, `KPM-REQ-011`, `KPM-REQ-012`, `KPM-REQ-014`
- Evidence class: executable SPipe definition; no execution summary is embedded.

## Scenarios
- runs lock and update through the production CLI with deterministic policy-bound output.
- preserves the admitted lock when resolution or policy validation fails.

## Manual Steps
- Generate and check the lock through the root simple command.
- Mutate the manifest and policy, then require attributed failures without publication.

## Selected Policy
- Manifest ownership: `simple.sdn`; ABI epoch: v1.
- Omitted overrides resolve to those selected values. `plugin.sdn`, deferred
  ABI values, and unknown policy strings are explicit rejection cases.

## Freshness
- Requirement IDs and scenario names mirror the executable source as of 2026-09-02.
- The executable contains no `pass_todo` or tautological `expect(true).to_equal(true)` evidence.
- Runtime execution was not available in this audit because the admitted self-hosted `bin/simple` lacks `test`; no runtime PASS is claimed.
