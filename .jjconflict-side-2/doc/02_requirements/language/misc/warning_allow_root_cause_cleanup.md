# Warning/Allow Root-Cause Cleanup

## Functional Requirements

- REQ-WARN-001: CI shall run the repository's strict Rust warnings-as-errors
  gate against `src/compiler_rust/`, not a removed legacy workspace path.
- REQ-WARN-002: CI shall provide one authoritative Simple lint lane that runs
  selected warning/allow cleanup canaries with `--deny-all`.
- REQ-WARN-003: The strict Rust gate shall compile the runtime primitive-sort
  test target cleanly before Clippy lint evaluation.
- REQ-WARN-004: The strict Rust gate shall not fail on the current
  `primitive_sort_bench` sort comparator style.
- REQ-WARN-005: The Rust lint checker shall recognize stdlib decorators
  `@variant`, `@immutable`, and `@no_gc` as known decorators.
- REQ-WARN-006: The repository shall include a canary spec that detects drift in
  the Rust workflow pathing, the Simple strict-lint lane wiring, and the current
  primitive-sort compile fix.

## Implementation Status (DONE — 2026-05-19, commit 461479c0af)

| Req | Task | Status |
|-----|------|--------|
| REQ-WARN-001 | A: repair Rust workflow pathing | DONE |
| REQ-WARN-002 | B: add Simple strict-lint lane | DONE |
| REQ-WARN-003 | C: fix primitive-sort test compile blockers | DONE |
| REQ-WARN-004 | C: fix primitive_sort_bench comparator warning | DONE |
| REQ-WARN-005 | D: decorator whitelist alignment | DONE |
| REQ-WARN-006 | E: regression canaries + deferred debt docs | DONE |

Allow count reduced from 1822 to 1714. All 3 canary spec tests pass.
Verify: PASS. 2 known WARNs documented as deferred debt (not blocking).
