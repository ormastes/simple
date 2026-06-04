# SPM Privilege Check Task Mirror Requirements

Feature: FR-SPM-0002.

## Functional Requirements

- REQ-SPM-0002-001: `sys_priv_check` case 110 must evaluate the privilege
  mirror registered for the caller task id.
- REQ-SPM-0002-002: The handler must return `1` only when the mirror covers
  the requested id-path bytes.
- REQ-SPM-0002-003: The handler must return `0` for missing mirrors,
  mismatched id paths, and empty id paths.
- REQ-SPM-0002-004: The privilege decision logic must be directly testable
  without constructing a full scheduler/syscall frame.
