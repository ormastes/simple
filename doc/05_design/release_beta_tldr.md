# Release Beta Design — TLDR

Six provenance-bound receipts prove the strict bootstrap, exact-CLI tools,
release checkers, seven platform artifacts, production verification, and the
completed GitHub prerelease.

## Core Shape

- `check-release-beta-readiness.shs` rejects missing, duplicate, malformed,
  mismatched, over-budget, draft, failed, or source-substituted evidence.
- Platform and GitHub receipts are derived by query/inspection scripts rather
  than manually asserted.
- Essential-tool evidence retains real test, lint, duplicate, and aggregate
  markers bound to the Stage 4 digest.
- Producer-job success permits publication; the completed remote run then
  permits final `release_beta_readiness_status=pass`.

## Operational Notes

- perf/RSS: Stage 3 ≤254 seconds; each strict stage ≤24 GiB max RSS.
- reruns: each acceptance gate runs once; green evidence is retained.

## Open Next

- [detail design](release_beta.md)
- [operator manual](../06_spec/03_system/app/release/feature/release_beta_spec.md)
- [system-test plan](../03_plan/sys_test/release_beta.md)
