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
- SDD-NFR-005: Diagram edit operations remain pure transformations over parsed
  SDD graphs and do not depend on GUI, filesystem, shell, or browser state.
- SDD-NFR-006: Parent/group membership must remain deterministic metadata. The
  canonical field is `parent`; user-facing "group" terminology must not create
  a second source of truth.
- SDD-NFR-007: Selection rendering and inspector reads must be pure derived
  views. Missing targets report `found=false` with a deterministic reason and
  must not mutate graph state.
