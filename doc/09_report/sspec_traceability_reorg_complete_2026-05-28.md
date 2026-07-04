# SSPEC Traceability Reorg Complete

Date: 2026-05-28

## Summary

The broad SSPEC/SPipe traceability reorganization is structurally complete.
Executable top-level test roots were moved into canonical buckets, generated
SPipe documentation now has a clear mirrored path rule, and the migration map
records the completed batches through the remaining app, OS, and library roots.

`sspec` remains an old name in historical paths and plan titles. New work should
use SPipe terminology.

## Final Test Root Shape

Current canonical top-level test buckets:

```text
test/baselines
test/feature
test/fixtures
test/integration
test/perf
test/shared
test/system
test/unit
```

No current top-level executable test roots are known to need migration after the
final audit.

## Documentation Updated

- `doc/03_plan/sspec_traceability_reorg_plan.md` now marks the structural reorg
  complete and keeps remaining items as follow-ups.
- `doc/03_plan/sspec_traceability_migration_map.md` now records completed
  batches through Batch 34.
- `doc/07_guide/testing/test_layout_traceability.md` is the operational guide
  for adding and moving tests under the canonical layout.
- `test/README.md` describes the canonical executable and support-data roots.

## Verification

Final structural checks:

```bash
git diff --check
find test -mindepth 1 -maxdepth 1 -type d -print | sort
find test/app test/lib test/os test/dbfs test/browser_engine test/web_platform test/reftest test/qemu test/riscv64_fpga test/fuzz test/js test/kernel test/nvfs test/tools -type f -print 2>/dev/null | sort
find doc/06_spec -maxdepth 1 -type f -print | sort
find doc/06_spec/legacy -maxdepth 1 -type f -print 2>/dev/null | sort
```

Results:

- `git diff --check` passed.
- Top-level `test/` contains only canonical buckets.
- Old top-level roots contain no files.
- Root `doc/06_spec/` contains only navigation and catalog/data files:
  `INDEX.md`, `README.md`, `bootstrap_test_gate.sdn`, `feature.md`,
  `feature_db.sdn`, and `pending_feature.md`.
- `doc/06_spec/legacy/` has no root files.

## Known Follow-Ups

- Some moved specs expose existing behavioral failures. They are recorded in
  the migration map and reorg plan verification sections.
- Previously tracked `.spipe_matchers_*` files under
  `test/01_unit/lib/nogc_async_mut/...` are ignored by `.gitignore`, so staging
  them requires `git add -f`.
- Root `doc/06_spec` catalog/data files should stay in place until their
  producers and consumers are traced.
