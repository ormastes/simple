# Seed: module name shadows match binding in `Ok(value): value`

**Status:** Open (read-path sites renamed on work/messenger-db-test-layers-20261031; other sites remain exposed)
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
