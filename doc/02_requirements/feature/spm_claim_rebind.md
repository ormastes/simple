# SPM Claim Rebind Requirements

Feature: FR-SPM-0003.

## Functional Requirements

- REQ-SPM-0003-001: Define syscall id 115 as `SysSpmClaim`.
- REQ-SPM-0003-002: The syscall must return `-1` when the caller lacks SPM
  claim privilege.
- REQ-SPM-0003-003: The syscall must rebind the boot placeholder SPM port to
  the real caller task and return `0`.
- REQ-SPM-0003-004: Repeated claims from the same task must be idempotent.
- REQ-SPM-0003-005: A second real task must be rejected with `-2`.
- REQ-SPM-0003-006: The SimpleOS SPM startup path must call the wrapper before
  entering its listen loop.
