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
