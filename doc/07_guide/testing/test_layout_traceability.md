# Test Layout And Traceability

Use this guide when adding, moving, or reviewing executable SPipe tests and
their generated docs.

## Canonical Test Roots

All executable tests should live under one of these top-level buckets:

| Root | Use for |
|---|---|
| `test/unit/` | Single module, function, parser, model, or command behavior. |
| `test/integration/` | Cross-module workflows that still run inside the normal host test runner. |
| `test/feature/` | User-visible language, app, browser, compatibility, or product feature behavior. |
| `test/system/` | End-to-end, QEMU, hardware-gated, process, OS, or multi-component workflows. |
| `test/shared/` | Import-free cross-platform specs marked `# @platform: all`. |

Support data belongs outside executable roots:

| Root | Use for |
|---|---|
| `test/fixtures/` | Helper modules, static source snippets, compatibility scripts, generated input, and preserved evidence that should not be discovered as standalone specs. |
| `test/baselines/` | Goldens and expected outputs consumed by tests. |
| `test/perf/` | Benchmark and performance-only checks. |

Do not add a new top-level test root unless the new role cannot fit these
buckets. Document the reason before adding the root.

## Mirrored SPipe Docs

Generated/manual SPipe docs mirror executable test paths after removing the
leading `test/` segment:

```text
test/<kind>/<domain>/<feature>_spec.spl
doc/06_spec/<kind>/<domain>/<feature>_spec.md
```

Examples:

```text
test/feature/usage/math_blocks_spec.spl
doc/06_spec/feature/usage/math_blocks_spec.md

test/system/qemu/qmp_screendump_spec.spl
doc/06_spec/system/qemu/qmp_screendump_spec.md
```

Root `doc/06_spec/` is reserved for navigation and catalog/data files. Generated
feature, unit, integration, system, and shared docs should not be added at the
root.

## Placement Rules

- Put direct source-module coverage under `test/unit/<source-area>/...`.
- Put app or library workflows under `test/integration/<area>/...` when they
  exercise multiple modules but do not require a full system environment.
- Put compatibility and feature acceptance coverage under `test/feature/...`.
- Put QEMU, FPGA, OS boot, disk-image, process, and hardware-gated checks under
  `test/system/...`.
- Put reusable helper modules, harness fragments, and scripts under
  `test/fixtures/...`.
- Keep `test/shared/` import-free except for built-in BDD helpers such as
  `describe`, `context`, `it`, and `expect`.

## Move Checklist

1. Move the executable spec and any adjacent `summary.txt` evidence together.
2. Move helper modules to `test/fixtures/...` instead of leaving them beside
   executable specs when they are not standalone scenarios.
3. Update exact path references in docs, test databases, source comments, and
   summary files.
4. Update module imports when the moved path is imported by another test.
5. Run focused discovery or execution for representative moved specs.
6. Run `git diff --check`.
7. Search for old exact paths before committing.

For ignored filenames that were previously tracked, such as
`.spipe_matchers_*`, use explicit staging when needed:

```bash
git add -f test/unit/lib/nogc_async_mut/**/.spipe_matchers_*.spl
```

## Current Migration State

The broad root migration is complete as of 2026-05-28. The only current
top-level test buckets are:

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

The detailed batch map is maintained in:

- `doc/03_plan/sspec_traceability_migration_map.md`
- `doc/03_plan/sspec_traceability_reorg_plan.md`
