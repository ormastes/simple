# LibreOffice Base NFR Requirements

## Requirements

- BASE-NFR-001: Base table operations are pure Simple logic with no filesystem,
  shell, browser, GUI, or network calls.
- BASE-NFR-002: Row-cell reads continue to use iteration-based access so
  non-first-column predicates avoid the known indexed-read runtime issue.
- BASE-NFR-003: Checked edits are deterministic and return explicit accepted,
  reason, affected-count, and table fields.
- BASE-NFR-004: The LLM catalog advertises only operations backed by implemented
  and tested Base APIs.
