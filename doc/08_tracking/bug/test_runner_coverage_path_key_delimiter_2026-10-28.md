# Test-runner coverage keys truncate valid pipe paths — 2026-10-28

## Status

Fixed in the accompanying source change; owner-specific Phase1 red/green evidence
is recorded below. This note is the bug record. The canonical bug database was
not modified.

## Defect

Both `src/app/test_runner_new/test_runner_coverage.spl` and
`src/lib/nogc_sync_mut/test_runner/test_runner_coverage.spl` serialize file paths
into counter keys using `|`, then split those keys on the same character. A
valid source path such as `src/a|b.spl` is read back as `src/a`; paths with the
same prefix can be merged into one per-file report entry. The std runner also
uses pipe-delimited zero-outcome receipt rows, so such a path made the row
ambiguous to `check_critical_branch_outcomes`.

## Fix

The internal path segment now percent-escapes `%` as `%25` and `|` as `%7C`, in
that order, and decodes in reverse order. Thus ordinary file paths retain their
existing key spelling, while a literal path containing `%7C` remains distinct
from a path containing `|`. The std runner uses the same encoding for outcome
receipt rows and decodes the path before critical-outcome matching. Rendered
coverage SDN still contains the original path.

## Reproduction and verification

The new owner-specific regressions failed against baseline code. The baseline
report showed `src/a|b.spl` and `src/a|c.spl` as `src/a, b.spl` and `src/a,
c.spl`, with shifted line and column fields. The std test also checks the
pipe-path zero-outcome receipt and critical-outcome checker.

Using retained Phase1 `aa58a24e…` without rebuilding the Phase2 compiler:

- `coverage_key_path_spec.spl`: baseline failed; fixed code passed 1/1.
- `coverage_key_path_std_spec.spl`: baseline failed; fixed code passed 1/1.
- Both cases cover delimiter paths, a literal `%7C` path, Unicode, ordinary
  paths, decision and condition counts, and rendered file paths.

`git diff --check` passed. The broad existing
`coverage_test_runner_spec.spl` still has three unrelated API mismatches:
its imported std module does not provide `render_coverage_sdn` or
`parse_coverage_sdn` (the current names are `render_coverage_state_sdn` and
`parse_coverage_state_sdn`). The focused regression avoids those old references.
