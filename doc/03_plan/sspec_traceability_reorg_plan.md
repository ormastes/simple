# Plan: SSPEC Traceability Reorganization

**Date:** 2026-05-28
**Status:** Structural Reorg Complete; Follow-ups Tracked

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
- Removed the remaining root-level generated math duplicates after updating the
  canonical mirrored `feature/usage` docs:
  `loss_nograd_blocks_spec.md`, `math_render_spec.md`, and the shorter
  `math_blocks_spec.md` root snapshot are no longer present at the
  `doc/06_spec/` root.
- Cleared `doc/06_spec/legacy/`: moved the live TRACE32 STM32H7 JIT doc to
  `doc/06_spec/feature/app/remote_jit/trace32_stm32h7_jit_e2e_spec.md` and
  removed stale legacy navigation plus old `test-spec` generated outputs.
- Repaired the pure-Simple `spipe-docgen` direct execution path. Direct
  interpreter-mode invocation now successfully generated
  `/tmp/spipe-docgen-probe/feature/language/placeholder_lambda_spec.md`.
- Moved low-risk top-level `test/hal`, `test/rtl`, `test/sffi`, and
  `test/runtime` specs into canonical unit/fixture buckets. Several moved
  RTL/SFFI/runtime specs are discovered at the new paths but still fail focused
  interpreter verification.
- Moved the shallow top-level `test/compiler` slice into canonical compiler
  unit buckets: auto-vector string semantics, MIR optimization specs, and VHDL
  hardware-spawn lowering. Auto-vector string and the MIR optimization specs
  pass focused verification; the moved VHDL spec is discovered but still fails
  17 examples.
- Moved the top-level `test/kernel` boot/loader specs to
  `test/system/kernel`. All four moved kernel specs pass focused verification
  at their new paths.
- Moved the top-level `test/fuzz` deterministic fuzz/property specs to
  `test/feature/language/fuzz` with summary evidence preserved. The moved fuzz
  directory passes focused verification.
- Moved top-level JS conformance specs to `test/feature/js` and moved the shell
  compatibility harness to `test/fixtures/js/compat_test.sh`. The moved JS
  specs are discovered at the new path but still fail existing conformance
  coverage.
- Moved top-level NVFS host-side storage specs to
  `test/integration/storage/nvfs`. The moved directory passes focused
  verification.
- Moved top-level tools specs into canonical `test/unit/tools` and
  `test/system/tools` buckets, with CI helpers and saved summaries preserved
  under `test/fixtures/tools`.
- Moved top-level DBFS storage specs to `test/integration/storage/dbfs` and
  support harnesses to `test/fixtures/storage/dbfs`.
- Moved top-level browser/rendering roots into canonical buckets:
  `test/browser_engine` to `test/unit/browser_engine`,
  `test/web_platform` to `test/feature/web_platform`, and `test/reftest` to
  `test/system/reftest`.
- Moved QEMU and FPGA hardware-gated roots into canonical system buckets:
  `test/qemu` to `test/system/qemu` and `test/riscv64_fpga` to
  `test/system/hardware/riscv64_fpga`.
- Moved top-level app specs into canonical `test/unit/app` and
  `test/integration/app` buckets, preserving summary evidence.
- Moved top-level OS specs into canonical `test/unit/os`,
  `test/integration/os`, `test/system/os`, and `test/fixtures/os` buckets.
- Moved the remaining top-level lib specs into canonical `test/unit/lib` and
  `test/fixtures/lib` buckets.

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
3. Reorganize remaining `test/` outliers after identifying source-area ownership:
   no known top-level executable roots remain from the current audit.
   `test/shared/`, `test/hal`, `test/rtl`, `test/runtime`, `test/sffi`, and
   the shallow `test/compiler` slice are resolved. `test/kernel` is also
   resolved under `test/system/kernel`; `test/fuzz` and `test/js` are resolved
   under feature/fixture buckets; `test/nvfs` is resolved under
   `test/integration/storage/nvfs`; `test/tools` is resolved under
   unit/system/fixture tools buckets; `test/dbfs` is resolved under
   storage integration/fixture buckets; `test/browser_engine`,
   `test/web_platform`, and `test/reftest` are resolved under
   unit/feature/system buckets; `test/qemu` and `test/riscv64_fpga` are
   resolved under system buckets; `test/app` is resolved under unit/integration
   app buckets; `test/os` is resolved under unit/integration/system/fixture OS
   buckets; `test/lib` is resolved under unit/fixture lib buckets.
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
- SPipe docgen direct generation:
  `SIMPLE_LIB=src SIMPLE_EXECUTION_MODE=interpret bin/simple --interpret src/app/spipe_docgen/main.spl test/feature/language/placeholder_lambda_spec.spl --output /tmp/spipe-docgen-probe`
  completed and generated the mirrored placeholder-lambda doc.
- Low-risk unit move: `test/unit/hal/hal_traits_spec.spl` passed 30/30 in the
  worker. `test/unit/rtl/encode_riscv_spec.spl`,
  `test/unit/sffi/sffi_public_api_spec.spl`,
  `test/unit/runtime/simd_text/simd_text_test.spl`, and
  `test/unit/runtime/simd_text/simd_text_fuzz_test.spl` were discovered at the
  new paths but failed focused interpreter verification.
- Compiler slice move: `test/unit/compiler/semantics/auto_vec_string_test.spl`
  and the moved MIR optimization specs under `test/unit/compiler/mir_opt/`
  passed focused interpreter verification in the worker. The moved
  `test/unit/compiler/vhdl/hardware_spawn_lower_spec.spl` is discovered but
  fails 17 examples.
- Kernel system move:
  `SIMPLE_LIB=src bin/simple test --force-rebuild test/system/kernel/boot_fs_mount_spec.spl`
  passed 8/8;
  `SIMPLE_LIB=src bin/simple test --force-rebuild test/system/kernel/boot_fs_spec.spl`
  passed 11/11;
  `SIMPLE_LIB=src bin/simple test --force-rebuild test/system/kernel/elf_load_chain_spec.spl`
  passed 6/6;
  `SIMPLE_LIB=src bin/simple test --force-rebuild test/system/kernel/nvfs_elf_load_spec.spl`
  passed 3/3.
- Fuzz feature move:
  `bin/simple test test/feature/language/fuzz --mode=interpreter --no-cache`
  passed 33/33 across three moved files.
- JS feature move: `bash -n test/fixtures/js/compat_test.sh` passed.
  `bin/simple test test/feature/js` discovered all four moved JS specs but
  failed existing JS conformance coverage with 0 passed and 114 failed.
- NVFS storage integration move:
  `SIMPLE_LIB=src bin/simple test --force-rebuild test/integration/storage/nvfs`
  passed 21/21 across five moved files.
- Tools move: representative moved specs passed:
  `test/unit/tools/echo_spec.spl` 5/5,
  `test/unit/tools/shell/seq_spec.spl` 3/3,
  `test/unit/tools/desktop/primary_cli_model_spec.spl` 3/3,
  `test/unit/tools/simple_os_primary_spec.spl` 4/4,
  `test/system/tools/manual/platform_spec_verification_spec.spl` 4/4, and
  `test/system/tools/deploy/smoke_spec.spl` 4/4. `test/unit/tools/cat_spec.spl`
  exited 0 with 4/4 summary but also printed a contradictory per-file
  `FAILED` line.
- DBFS storage integration move: representative moved specs passed:
  `test/integration/storage/dbfs/dbfs_recovery_spec.spl` 9/9,
  `test/integration/storage/dbfs/dbfs_no_regression_spec.spl` 5/5,
  `test/integration/storage/dbfs/dbfs_driver_spec.spl` 8/8,
  `test/integration/storage/dbfs/fts_engine_spec.spl` 28/28, and
  `test/integration/storage/dbfs/dbfs_engine_wal_spec.spl` 8/8. Existing
  DB/SQL specs still fail after the move: `pure_db_spec.spl` reported 41
  passed and 18 failed, and `pure_db_sql_extended_spec.spl` reported 8 passed
  and 2 failed.
- Browser/web/reftest move: discovery passed for
  `test/unit/browser_engine` with 252 listed tests,
  `test/feature/web_platform` with 398 listed tests, and
  `test/system/reftest` with 35 listed tests.
  `test/system/reftest/parity/pixel_diff_core_spec.spl` passed 15/15.
  Existing focused failures remain in browser-engine net, web-platform
  scorecard, and reftest parity behavior checks.
- QEMU/FPGA system move:
  `test/unit/lib/test_runner/test_classification_system_routing_spec.spl`
  passed 9/9, `test/system/qemu/qmp_screendump_spec.spl` passed 5/5,
  `test/unit/qemu/qemu_harness_acquire_or_spawn_spec.spl` passed 8/8, and
  `test/system/hardware/riscv64_fpga` passed 91/91.
- App move: discovery passed for `test/unit/app/itf` with 219 listed tests,
  `test/unit/app/svim` with 72 listed tests, `test/integration/app/ui.web`
  with 158 listed tests, and `test/integration/app/diagnostics` with 13 listed
  tests. Focused checks passed for `test/unit/app/itf/itf_flags_spec.spl`
  10/10 and `test/integration/app/ui.web/random_hex_test.spl` 8/8. Existing
  behavioral failures remain in `test/unit/app/svim/core_spec.spl` and
  `test/unit/app/ui.test_api/handler_test.spl`.
- OS move: focused checks passed for
  `test/system/os/desktop/taskbar_shell_qemu_test.spl` 12/12 and
  `test/integration/os/port/disk_image_bake_spec.spl` 8/8. Discovery passed
  for `test/unit/os/kernel` with 1136 listed tests,
  `test/integration/os/port` with 73 listed tests, and `test/system/os/port`
  with 36 listed tests. Existing failures remain in moved stack builder,
  bootstrap cross status, disk boot, syscall shim, Simple-from-FS, and HAL
  trait-surface specs; compositor web-surface blit hung and was killed. The
  moved `test/unit/os/kernel/logging/marker_wire_format_spec.spl` exists but
  runner discovery reported 0 files.
- Lib move: discovery passed for `test/unit/lib/blink` with 182 listed tests
  and `test/unit/lib/transitive` with 1 listed test.
  `test/unit/lib/transitive/transitive_import_spec.spl` passed 1/1. Existing
  failures remain in moved common Wine substrate, MCP lazy loading, Skia
  matrix, HAL types, text length, bytes pointer, and ECS specs. The moved
  `.spipe_matchers_*` files under `test/unit/lib/nogc_async_mut/...` are
  ignored by `.gitignore`, so staging will require force-adding those
  previously tracked matcher files.
- Broader `bin/simple check` was attempted for docgen files but hung in the
  workspace check/test path and was terminated.
