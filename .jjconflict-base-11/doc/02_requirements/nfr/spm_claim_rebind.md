# SPM Claim Rebind NFR

Feature: FR-SPM-0003.

## Non-Functional Requirements

- NFR-SPM-0003-001: The claim path must not allocate on the hot SPM message
  send/listen paths.
- NFR-SPM-0003-002: The claim gate must reuse the existing privilege mirror
  model instead of adding a second authorization store.
- NFR-SPM-0003-003: The placeholder rebind must clear stale placeholder inbox
  state before assigning the real SPM task.
