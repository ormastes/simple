# Seed: module name shadows match binding in `Ok(value): value`

**Status:** Fixed (stale). 2026-11-04: dense_storage_rows_spec.spl 8/8 pass on the seed; a minimal `use std.common.json.value` + `case Ok(value): value` repro passes in both run and test modes. Read-path sites were renamed earlier.
**Severity:** P2
**Date:** 2026-10-31

## Symptom

On the Phase 1 seed in spec mode, when a program imports `std.common.json.value`, the module name `value` takes precedence over a match binding named `value` in `case Ok(value): value`. The program fails with `tuple index access on non-tuple type i64`.

## Evidence

- Read-path sites were renamed on work/messenger-db-test-layers-20261031.
- `git grep -c "Ok(value): value" -- src/lib` reports 517 sites across 112 files (counted 2026-10-31).

## Unverified

- Whether the same shadowing happens outside spec mode or on a rebuilt compiler.
- Whether all 517 sites are reachable from a program that imports `std.common.json.value`. The count is of text matches, not of reachable call sites.

## 2026-11-04 re-verification: NOT REPRODUCIBLE (closed stale)

On the current seed (bin/simple.exe, release/1.0.0 80f074e5782+), both the
original spec `test/02_integration/app/devhub/messenger/dense_storage_rows_spec.spl`
(8/8 pass, including json-value import) and a minimal spec that imports
`std.common.json.value` and matches `case Ok(value): value` (new
`test/01_unit/compiler/seed/module_name_vs_match_binding_spec.spl`, 1/1) pass,
in both `run` and `test` mode. The 517-site count is moot: the shadowing no
longer occurs. If it recurs, the new spec fails first.
