# Local Research: Test Folder Organization

**Date:** 2026-05-28
**Scope:** Documentation-only research for `test/` layout rules. No test files were moved.

## Current Shape

- `test/unit/`, `test/integration/`, `test/feature/`, and `test/system/` are the
  documented canonical executable SPipe buckets.
- The current tree also contains legacy executable top-level directories outside
  those buckets, including `test/perf/`, `test/os/`, `test/app/`,
  `test/tools/`, `test/dbfs/`, `test/qemu/`, `test/reftest/`,
  `test/browser_engine/`, `test/web_platform/`, `test/code_quality/`,
  `test/sys/`, and smaller single-purpose roots.
- `test/lib/` is mixed: it supports source imports, but it also contains many
  executable `.spl` files today.
- Support-data roots such as `test/baselines/` and `test/fixtures/` are not
  executable category roots and need separate treatment from SPipe placement
  rules. `test/features/` and `test/data/` have since been cleared by moving
  support inputs under `test/fixtures/`.
- `test/shared/` is executable SPipe coverage for `# @platform: all`
  cross-platform specs. It is not a fixture root; keep or migrate it only with
  the platform-runner contract in mind.
- The two root-level executable specs found during this research were resolved
  in the first cleanup slice:
  - `test/serpent_check_spec.spl` was byte-for-byte identical to
    `test/unit/os/crypto/serpent_kat_spec.spl` and was removed as a duplicate.
  - `test/test_while_basic_spec.spl` moved to
    `test/unit/compiler/control_flow/while_basic_spec.spl` with mirrored doc
    `doc/06_spec/unit/compiler/control_flow/while_basic_spec.md`.
- The legacy `test/cli/` bucket was resolved by moving files according to their
  `@cover` target:
  - `theme_sync_diff_test.spl` and `theme_sync_dump_local_test.spl` moved under
    `test/unit/lib/ui/theme_sync/`.
  - `theme_sync_list_test.spl` moved under
    `test/unit/app/cli/theme_sync/`.
  - Mirrored manual/spec docs were added under the matching `doc/06_spec/unit/...`
    paths.
- The legacy `test/specs/` bucket was resolved as language feature coverage:
  executable specs and their `summary.txt` evidence directories moved under
  `test/feature/language/`, and root language docs moved under
  `doc/06_spec/feature/language/*_spec.md`.
- The legacy `test/data/` support bucket was resolved by moving the agent
  roundtrip fixture to `test/fixtures/data/agents/test_roundtrip_001.txt`.

## Rules Inferred From Current Documentation

- New unit tests should go under `test/unit/<source-area>/...`.
- New cross-module tests should go under `test/integration/<source-area>/...`.
- New user-visible feature BDD tests should go under
  `test/feature/<domain>/...`.
- New end-to-end workflows should go under `test/system/<domain>/...`.
- Generated SPipe docs should mirror the executable test path under
  `doc/06_spec/` after removing the leading `test/` segment.

## Outliers To Handle In The Reorg

- Decide whether legacy domain roots such as `test/perf/`, `test/qemu/`,
  `test/reftest/`, `test/browser_engine/`, and `test/web_platform/` remain
  named suites or migrate into canonical category buckets.
- Separate import/support assets from executable specs under `test/lib/` and
  `test/fixtures/`. Treat `test/shared/` as a cross-platform executable tier
  until the runner and testing guide define a replacement.
- Root-level `.spl` specs plus legacy `test/cli/` and `test/specs/` buckets are
  now cleared; keep this invariant by placing new executable specs under
  `unit/`, `integration/`, `feature/`, or `system/`.
