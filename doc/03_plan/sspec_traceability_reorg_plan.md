# Plan: SSPEC Traceability Reorganization

**Date:** 2026-05-28
**Status:** In Progress

## Goal

Make SSPEC/manual docs, executable tests, requirements, research, design,
architecture, plans, implementation, guides, and verification evidence traceable
by a stable folder and feature-slug convention.

## Rule

Generated/manual SPipe docs mirror executable test paths:

`test/<kind>/<domain>/<feature>_spec.spl` ->
`doc/06_spec/<kind>/<domain>/<feature>_spec.md`

## Completed Slice

- Documented the canonical `doc/06_spec` mirrored layout.
- Documented matching `test/` organization and traceability rules.
- Updated `$design`, `$impl`, `$system_test`, and `$verify` skill instructions.
- Updated `spipe-docgen` to write nested output paths from source spec paths.
- Added focused coverage for the nested `math_blocks_spec` output path.
- Added a migration map for root-level and legacy `doc/06_spec` files:
  `doc/03_plan/sspec_traceability_migration_map.md`.
- Added local research for current `test/` folder organization and outliers:
  `doc/01_research/local/test_folder_organization.md`.
- Added traceability warnings for mirrored generated spec docs:
  - `TRC231`: executable spec is missing its mirrored `doc/06_spec/...` doc.
  - `TRC232`: generated doc uses a flat or mismatched legacy path.
- Added `skip_it` scenario-body rendering coverage in `spipe-docgen`.
- Migrated the first high-confidence root/legacy generated-doc batch into
  mirrored paths for `feature/usage`, `integration/remote_jit`, and
  `unit/app/tooling`.
- Cleared root-level executable `.spl` tests:
  - removed duplicate `test/serpent_check_spec.spl` because
    `test/unit/os/crypto/serpent_kat_spec.spl` is identical,
  - moved `test/test_while_basic_spec.spl` to
    `test/unit/compiler/control_flow/while_basic_spec.spl`,
  - added mirrored doc
    `doc/06_spec/unit/compiler/control_flow/while_basic_spec.md`.
- Cleared legacy `test/cli/` by moving theme-sync tests under canonical unit
  buckets based on their `@cover` source targets and adding mirrored
  `doc/06_spec/unit/...` docs.
- Cleared legacy `test/specs/` by classifying the extracted language specs as
  `test/feature/language/`, moving their `summary.txt` evidence directories
  with them, and moving root language docs to
  `doc/06_spec/feature/language/*_spec.md`.
- Moved stale root docs for sandboxing, shell API, metaprogramming, and types to
  mirrored `doc/06_spec/feature/...` paths and updated their source links from
  deleted `tests/specs/...` paths.
- Moved high-confidence root docs for math blocks and remote baremetal feature
  specs to mirrored `doc/06_spec/feature/...` paths, and removed identical
  duplicate math-block generated docs under `doc/06_spec/app/compiler/...`.
- Moved the root syntax generated snapshot to
  `doc/06_spec/feature/usage/syntax_spec.md`, matching
  `test/feature/usage/syntax_spec.spl`.
- Moved the web-dashboard app spec bucket from `test/app/web_dashboard/` to
  `test/feature/app/web_dashboard/`, moved its existing root generated docs to
  mirrored `doc/06_spec/feature/app/web_dashboard/` paths, and added scenario
  docs for the remaining moved web-dashboard specs.
- Moved the tmux stdlib unit spec from `test/unit/lib/std/tmux/` to
  `test/unit/lib/std/tmux/`, and moved its generated doc to
  `doc/06_spec/unit/lib/std/tmux/tmux_api_spec.md`.
- Replaced the stale root tensor-dimensions generated snapshot with executable
  SPipe traceability coverage at `test/feature/ml/tensor_dimensions_spec.spl`
  and mirrored doc `doc/06_spec/feature/ml/tensor_dimensions_spec.md`.
- Moved the remaining legacy stdlib unit spec bucket from `test/lib/std/unit/`
  to `test/unit/lib/std/`, preserving existing summary evidence directories.
- Cleared the remaining executable `test/lib/std/` tree:
  - `features/placeholder_lambda` moved to `test/feature/language/`,
  - `integration/*` moved to `test/integration/lib/std/`,
  - `spec/decorators` moved to `test/unit/lib/std/spec/`,
  - `type_checker/*` moved to `test/unit/lib/std/type_checker/`.
  Existing summary evidence directories were moved and their embedded spec paths
  updated.
- Removed the top-level `test/smoke/` alias by moving
  `compile_smoke_spec.spl` to `test/system/smoke/` and deleting its obsolete
  hidden `.sspec` wrapper artifact.
- Removed tracked temporary verifier-quality fixtures from
  `test/tmp_verify_quality/` and `src/tmp_verify_quality/`. The verifier
  integration spec now creates those intentionally bad snippets under
  `build/test-fixtures/verify_quality/` at runtime.
- Removed top-level `test/scratch/` and `test/spike/`. Parser-safe generic
  repros are now active SPipe coverage in
  `test/feature/language/generic_repro_spec.spl`; the parser-failing generic
  BTree spike is preserved as a fixture and tracked as a bug.
- Removed the `test/sys/` alias by moving wm_compare system specs and goldens
  to `test/system/wm_compare/`, and SimpleOS driver/display specs to
  `test/system/simpleos/`. Added mirrored `doc/06_spec/system/...` docs for the
  moved specs. The move also exposed real wm_compare failures, now tracked in
  `doc/08_tracking/bug/wm_compare_system_specs_visible_failures.md`.
- Removed the plural `test/features/` alias. Its `.feature` files are
  feature-request fixtures rather than executable SPipe specs, so they moved to
  `test/fixtures/feature_requests/`.
- Removed the top-level `test/bench/` alias by moving direct benchmark scripts
  to `test/perf/bench/`.
- Removed small top-level `test/stats/`, `test/lint/`, and `test/util/`
  aliases. Stats specs moved to `test/unit/app/stats/`; lint and repro scripts
  moved under `test/fixtures/`.
- Removed top-level `test/code_quality/` by moving the quality-gate canary
  specs to `test/system/code_quality/`.
- Removed top-level `test/data/` by moving the agent roundtrip support fixture
  to `test/fixtures/data/agents/` and changing the synthetic IO path in
  `test/integration/app/io_intensive_spec.spl` to the fixture namespace.
- Kept `test/shared/` as the canonical executable cross-platform tier for
  `# @platform: all` SPipe specs. Runner discovery now treats shared specs as
  unit-level coverage, the platform filter accepts `# @platform: all` in normal
  interpreter mode, and focused single-file/directory runs discover and execute
  shared specs.
- Moved the non-shared contract testing spec out of `test/shared/` to
  `test/unit/lib/common/contracts/contract_testing_spec.spl`, preserved its
  summary evidence, added the mirrored
  `doc/06_spec/unit/lib/common/contracts/contract_testing_spec.md`, and
  clarified that shared specs may use the built-in `context` BDD helper.

## Restart Checkpoint

- Current safe stopping point: `test/shared/` is canonical and runner-visible.
- Do not move `test/shared/` into `test/unit/shared/`; it is a documented
  platform tier, not a fixture or generic unit bucket.
- Shared zero-import follow-up is resolved for the known hard violation:
  `test/shared/` now has no `use` imports. The strict guide wording now
  includes built-in `context`, matching existing shared BDD usage.
- Obsolete SStack skill install check: active `.claude`, `.codex`, and
  `.agents` skill trees no longer expose `sstack`; stale cached
  `.spipe/spipe/.../sstack*` copies were removed. Historical tracking docs
  still mention SStack and were not rewritten.

## Next Slices

1. Continue moving or regenerating high-confidence root/legacy docs only after
   source spec ownership is known. Regenerate files with stale source headers
   instead of moving them as-is.
2. Route normal doc generation and test-generated docs through the mirrored
   pure-Simple `spipe-docgen` path.
3. Reorganize `test/` outliers after identifying source-area ownership:
   `test/lib/` executable files and transitional top-level suites such as
   `test/app`, `test/dbfs`, `test/browser_engine`, and `test/web_platform`.
   `test/shared/` is resolved and should remain in place.
4. Add release/verify guidance for when `TRC231`/`TRC232` should be hard
   failures instead of warnings.
5. Compare or regenerate non-identical legacy docs for placeholder lambda,
   decorators, and type-checker specs before deleting duplicate generated docs.

## Verification

- Focused unit: `SIMPLE_LIB=src bin/simple test --force-rebuild test/unit/app/tooling/spipe_docgen_scenario_body_spec.spl`
- Focused unit: `SIMPLE_LIB=src bin/simple test --force-rebuild test/unit/app/tooling/traceability_spec.spl`
- Moved stdlib feature: `SIMPLE_LIB=src bin/simple test --force-rebuild test/feature/language/placeholder_lambda_spec.spl`
- Moved stdlib unit: `SIMPLE_LIB=src bin/simple test --force-rebuild test/unit/lib/std/spec/decorators_spec.spl`
- Moved stdlib unit: `SIMPLE_LIB=src bin/simple test --force-rebuild test/unit/lib/std/type_checker/type_inference_spec.spl`
- Moved stdlib unit: `SIMPLE_LIB=src bin/simple test --force-rebuild test/unit/lib/std/type_checker/type_inference_v2_spec.spl`
- Moved stdlib integration: `SIMPLE_LIB=src bin/simple test --force-rebuild test/integration/lib/std/diagram/diagram_integration_spec.spl`
- Moved stdlib integration: `SIMPLE_LIB=src bin/simple test --force-rebuild test/integration/lib/std/doctest/discovery_spec.spl`
- Moved stdlib integration: `SIMPLE_LIB=src bin/simple test --force-rebuild test/integration/lib/std/failsafe/crash_prevention_spec.spl`
- Moved stdlib integration: `SIMPLE_LIB=src bin/simple test --force-rebuild test/integration/lib/std/improvements/stdlib_improvements_spec.spl`
- Moved stdlib integration: `SIMPLE_LIB=src bin/simple test --force-rebuild test/integration/lib/std/ml/simple_math_integration_spec.spl`
- Moved stdlib integration: `SIMPLE_LIB=src bin/simple test --force-rebuild test/integration/lib/std/screenshot/screenshot_ffi_spec.spl`
- Smoke alias cleanup: `SIMPLE_LIB=src bin/simple test --force-rebuild test/system/smoke/compile_smoke_spec.spl`
- Verifier fixture cleanup: `SIMPLE_LIB=src bin/simple test --force-rebuild test/integration/app/verify_test_quality_gate_spec.spl`
- Generic repro cleanup: `SIMPLE_LIB=src bin/simple test --force-rebuild test/feature/language/generic_repro_spec.spl`
- Small-root cleanup: `SIMPLE_LIB=src bin/simple test --force-rebuild test/unit/app/stats/benchmark_ledger_spec.spl test/unit/app/stats/inventory_classifier_spec.spl`
- System alias cleanup: `SIMPLE_LIB=src bin/simple test --force-rebuild test/system/simpleos/driver_acceleration_perf_spec.spl`
- System alias cleanup: `SIMPLE_LIB=src bin/simple test --force-rebuild test/system/simpleos/display_dma_contract_spec.spl`
- System alias cleanup: `SIMPLE_LIB=src bin/simple test --force-rebuild test/system/wm_compare/html_compat_spec.spl`
- System alias cleanup: `SIMPLE_LIB=src bin/simple test --force-rebuild test/system/wm_compare/emulated_capture_spec.spl`
- System alias cleanup: `SIMPLE_LIB=src bin/simple test --force-rebuild test/system/wm_compare/famous_site_engine2d_backend_spec.spl`
- Known FAIL after matcher/import cleanup: `test/system/wm_compare/v1_v2_parity_spec.spl`, `golden_gate_spec.spl`, `v1_v3_parity_spec.spl`, `v1_v4_parity_spec.spl`.
- Data fixture cleanup: `SIMPLE_LIB=src bin/simple test --force-rebuild test/integration/app/io_intensive_spec.spl`
- Shared runner unit coverage: `SIMPLE_LIB=src bin/simple test --force-rebuild test/unit/app/test_runner/execution_strategy_reclassify_spec.spl`
- Shared runner unit coverage: `SIMPLE_LIB=src bin/simple test --force-rebuild test/unit/app/test_runner_new/test_categorization_spec.spl`
- Shared runner single-file coverage: `SIMPLE_LIB=src bin/simple test --force-rebuild test/shared/core/primitives_spec.spl`
- Shared runner directory coverage: `SIMPLE_LIB=src bin/simple test --force-rebuild test/shared/core`
- Shared import audit: `rg -n '^use ' test/shared` returned no matches.
- Moved contract unit coverage: `SIMPLE_LIB=src bin/simple test --force-rebuild test/unit/lib/common/contracts/contract_testing_spec.spl`
- Shared types coverage after contract move: `SIMPLE_LIB=src bin/simple test --force-rebuild test/shared/types`
- Broader `bin/simple check` was attempted for docgen files but hung in the
  workspace check/test path and was terminated.
