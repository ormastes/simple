# Complete Build/Test Abnormality Acceptance Coverage

Status: open. The feature system spec contains real assertions, but it is not
yet a complete acceptance suite and has not passed admitted self-hosted Stage 4
verification.

Owner: perf/test-runner maintainer. Platform receipt rows additionally require
the runtime/process provider maintainer and prepared Windows/macOS hosts.

## Missing executable acceptance rows

- [ ] REQ-005: run the normal test runner and assert stable test identity plus
  persisted setup/compile/execution, resource class, cohort, budget, and anomaly
  fields from the production database write path.
- [ ] REQ-006: run a real build and assert stable subject/policy records,
  hierarchical spans, phase/work counters, and artifact digests persist and
  round-trip.
- [ ] REQ-007: execute interpreter/native and differing aspect/configuration
  cases and prove their canonical cohort IDs differ; prove incompatible cohorts
  cannot be promoted or compared together.
- [ ] REQ-011: exercise each standard resource class and explicit quantity;
  prove deterministic enforcement and that historical recommendations cannot
  loosen an explicit budget.
- [ ] REQ-014: execute `simple perf record`, `compare`, `explain`, and
  `baseline promote` through the public CLI and prove they read/write the same
  evidence used by normal build/test policy.
- [ ] Add a production-path approved-baseline lifecycle scenario covering
  Provisional -> Approved -> Suspect -> Superseded, immutable generation
  history, exact-cohort filtering, and failed-run exclusion.
- [ ] Replace synthetic-only cgroup event parsing as acceptance evidence with
  live provider fixtures wherever the host supports them; retain deterministic
  parser checks as unit tests.
- [ ] Complete and run the Windows Job Object rows in
  `simple_build_test_abnormality_windows_job_receipt_2026-08-24.md`.
- [ ] Complete and run the macOS process-group rows in
  `simple_build_test_abnormality_macos_receipt_2026-08-24.md`.

## Completion gate

1. Every REQ-001 through REQ-014 has at least one production-path executable
   system-test row with a falsifiable assertion and explicit `# @req` tag.
2. No `pass_todo`, tautological assertion, empty scenario, or fabricated
   unavailable resource value exists in the acceptance suite.
3. The executable spec regenerates its manual successfully with an admitted
   self-hosted compiler.
4. Focused specs and the production-readiness verifier report `STATUS: PASS`.
5. Windows/macOS rows either pass on their qualification hosts or remain
   explicitly unaccepted; unsupported fallback behavior is not platform parity.

Resume from
`test/03_system/app/perf/feature/simple_build_test_abnormality_detection_spec.spl`
and `doc/03_plan/sys_test/simple_build_test_abnormality_detection.md`. Do not
mark AC-3, AC-12, AC-13, or the feature complete until this checklist closes.
