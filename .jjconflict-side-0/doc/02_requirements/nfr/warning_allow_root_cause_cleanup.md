# Warning/Allow Root-Cause Cleanup NFR

- NFR-WARN-001: Authoritative lint lanes must fail hard on owned regressions and
  must not downgrade those failures to warnings.
- NFR-WARN-002: The initial Simple strict lane shall stay narrow enough to pass
  reliably on the current branch without depending on advisory editor/demo
  workflows.
- NFR-WARN-003: Remaining suppression debt not removed in this slice shall be
  documented as follow-up work rather than hidden behind broken enforcement.
- NFR-WARN-004: Regression canaries for the enforcement wiring shall run fast
  enough to fit inside normal CI checks.

## Verification Outcome (DONE — 2026-05-19, commit 461479c0af)

| NFR | Result |
|-----|--------|
| NFR-WARN-001 | PASS — both Rust and Simple lanes fail-hard on regressions |
| NFR-WARN-002 | PASS — Simple lane scoped to 3 stable code_quality canaries; no advisory workflows required |
| NFR-WARN-003 | PASS — `@extern unknown_attribute` and lint-wrapper segfault documented as deferred debt, not hidden |
| NFR-WARN-004 | PASS — 3 canary specs run within normal `bin/simple test` budget |
