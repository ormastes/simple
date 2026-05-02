# SPM Privilege Check Task Mirror NFR

Feature: FR-SPM-0002.

## Non-Functional Requirements

- NFR-SPM-0002-001: The syscall path must not add heap allocations beyond the
  existing id-path copy-in.
- NFR-SPM-0002-002: The implementation must reuse the existing privilege bridge
  lookup and two-gate check semantics.
- NFR-SPM-0002-003: Tests must cover allow, deny, no-mirror, and empty-path
  outcomes.
