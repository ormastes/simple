# SDD Diagram Editor NFR Requirements

## Requirements

- SDD-NFR-001: Parsing and rendering are pure Simple logic with no filesystem,
  shell, browser, or network calls.
- SDD-NFR-002: Existing relationship-only SDN graph blocks remain backward
  compatible.
- SDD-NFR-003: Rendered HTML is deterministic and escapes all user-controlled
  labels and attributes.
- SDD-NFR-004: Generated manuals remain under `doc/06_spec`, and executable
  specs remain under `test/`.
