# SPipe Traceability Migration Map

Date: 2026-05-28

Scope: planning and restart map for the former `sspec` documentation/test
layout. `sspec` is obsolete; use SPipe names for new work. Do not move files
from this map until the source SPipe owner is confirmed and the generated
markdown path can be regenerated or moved without losing traceability metadata.

## Status

**Map current; migration incomplete.** This map now reflects the current tree,
including completed batches and remaining root/legacy files requiring
decisions. Resolve the open items below before more broad `doc/06_spec/` or
`test/` movement.

Current root/legacy audit from the worktree:

| Area | Current state | Required action |
|---|---|---|
| Root navigation | `doc/06_spec/INDEX.md`, `doc/06_spec/README.md` | Keep at root. |
| Root data/catalog | `bootstrap_test_gate.sdn`, `feature.md`, `feature_db.sdn`, `pending_feature.md` | Trace producers/consumers before moving. |
| Root generated math docs | `loss_nograd_blocks_spec.md`, `math_blocks_spec.md`, `math_render_spec.md` | Compare with mirrored `doc/06_spec/feature/usage/*` and compiler legacy copies; keep one canonical generated doc per source spec. |
| Legacy generated index | `legacy/test-spec.md`, `legacy/test-spec.html` | Delete or archive after confirming no doc-nav fixture depends on them. |
| Legacy live TRACE32 doc | `legacy/trace32_stm32h7_jit_e2e_spec.md` | Regenerate/move to `doc/06_spec/feature/app/remote_jit/trace32_stm32h7_jit_e2e_spec.md`. |
| Runtime manual contract | `runtime/rt_gui_glass_contract.md` | Decide whether it is a manual runtime contract or needs an executable source spec. |
| Generated/category folders | `generated/pending_feature.md`, `categories/*.md`, `diagrams/.gitkeep` | Leave until generator ownership is traced. |

Current `test/` top-level roots still needing policy/migration review:
`test/app`, `test/browser_engine`, `test/compiler`, `test/dbfs`, `test/fuzz`,
`test/hal`, `test/js`, `test/kernel`, `test/lib`, `test/nvfs`, `test/os`,
`test/qemu`, `test/reftest`, `test/riscv64_fpga`, `test/rtl`,
`test/runtime`, `test/sffi`, `test/tools`, and
`test/web_platform`. `test/baselines`, `test/fixtures`, `test/perf`,
`test/shared`, `test/system`, `test/unit`, `test/integration`, and
`test/feature` already have an explicit role.

## Current Shape

- Canonical spec docs mostly live under mirrored subtrees, but legacy
  `doc/06_spec/app/compiler/...` docs still coexist with newer
  `doc/06_spec/feature/...`, `unit/...`, `integration/...`, and `system/...`
  docs.
- Root-level `doc/06_spec` currently has nine files: two navigation docs, four
  catalog/data files, and three generated math docs that still need a duplicate
  comparison decision.
- Additional legacy buckets: `doc/06_spec/legacy/*` and
  `doc/06_spec/runtime/rt_gui_glass_contract.md`.
- `doc/06_spec/README.md` now defines mirrored layout from `test/...` to
  `doc/06_spec/...`; use that rule for all migrations below.

## Migration Rules

- Preserve root `doc/06_spec/README.md` and `doc/06_spec/INDEX.md` as navigation.
- Treat `.sdn` files as data inputs until their generating/consuming tool is
  identified; do not rename them with generated markdown.
- Move generated markdown only when the source `test/..._spec.spl` owner is
  known.
- Prefer regeneration into the canonical path over manual markdown moves when
  `summary.txt` evidence exists beside a source spec.
- Before deleting a root-level duplicate, compare generated content against the
  canonical destination and keep the version with source/requirement links.

## Completed Migration Batches

### 2026-05-28 Batch 1

Moved high-confidence one-to-one generated/manual specs whose executable source
path was known and whose mirrored target did not already exist. Current audit:
the root math docs from this batch still exist and are non-identical to their
mirrored copies, so they remain open duplicate-resolution items.

| Old path | New mirrored path |
|---|---|
| `doc/06_spec/loss_nograd_blocks_spec.md` | `doc/06_spec/feature/usage/loss_nograd_blocks_spec.md` (open duplicate; root still exists) |
| `doc/06_spec/math_render_spec.md` | `doc/06_spec/feature/usage/math_render_spec.md` (open duplicate; root still exists) |
| `doc/06_spec/ch32v307_composite_runner_path_spec.md` | `doc/06_spec/integration/remote_jit/ch32v307_composite_runner_path_spec.md` |
| `doc/06_spec/qemu_rv32_raw_injected_regression_spec.md` | `doc/06_spec/integration/remote_jit/qemu_rv32_raw_injected_regression_spec.md` |
| `doc/06_spec/legacy/command_dispatch_spec.md` | `doc/06_spec/unit/app/tooling/command_dispatch_spec.md` |
| `doc/06_spec/legacy/test_runner_simple_spec.md` | `doc/06_spec/unit/app/tooling/test_runner_simple_spec.md` |

Deferred from this batch:

- `doc/06_spec/sandboxing.md` and `doc/06_spec/shell_api.md` were resolved in
  Batch 3.
- Duplicate math-block docs still need content comparison before root copies are
  removed.
- SDN/catalog files remain in place until producers and consumers are traced.

### 2026-05-28 Batch 2

Resolved the legacy `test/specs/` bucket by treating it as extracted language
feature coverage. Executable specs and their `summary.txt` evidence directories
moved to `test/feature/language/`; root language docs moved to
`doc/06_spec/feature/language/*_spec.md`.

| Old path | New mirrored path |
|---|---|
| `doc/06_spec/async_default.md` | `doc/06_spec/feature/language/async_default_spec.md` |
| `doc/06_spec/capability_effects.md` | `doc/06_spec/feature/language/capability_effects_spec.md` |
| `doc/06_spec/concurrency.md` | `doc/06_spec/feature/language/concurrency_spec.md` |
| `doc/06_spec/data_structures.md` | `doc/06_spec/feature/language/data_structures_spec.md` |
| `doc/06_spec/functions.md` | `doc/06_spec/feature/language/functions_spec.md` |
| `doc/06_spec/macro.md` | `doc/06_spec/feature/language/macro_spec.md` |
| `doc/06_spec/memory.md` | `doc/06_spec/feature/language/memory_spec.md` |
| `doc/06_spec/modules.md` | `doc/06_spec/feature/language/modules_spec.md` |
| `doc/06_spec/suspension_operator_spec.md` | `doc/06_spec/feature/language/suspension_operator_spec.md` |
| `doc/06_spec/traits.md` | `doc/06_spec/feature/language/traits_spec.md` |
| `doc/06_spec/type_inference.md` | `doc/06_spec/feature/language/type_inference_spec.md` |

Removed duplicate root `doc/06_spec/suspension_operator.md`; the active
executable scenario doc is now
`doc/06_spec/feature/language/suspension_operator_spec.md`.

### 2026-05-28 Batch 3

Resolved four stale root docs that still pointed at deleted `tests/specs/...`
sources by moving them to mirrored paths and updating source/update commands.

| Old path | New mirrored path |
|---|---|
| `doc/06_spec/sandboxing.md` | `doc/06_spec/feature/usage/sandboxing_spec.md` |
| `doc/06_spec/metaprogramming.md` | `doc/06_spec/feature/usage/metaprogramming_spec.md` |
| `doc/06_spec/types.md` | `doc/06_spec/feature/usage/types_spec.md` |
| `doc/06_spec/shell_api.md` | `doc/06_spec/feature/app/shell_api_spec.md` |

Older duplicate copies under `doc/06_spec/app/compiler/...` remain for a later
comparison pass.

### 2026-05-28 Batch 4

Resolved high-confidence root docs whose executable specs already live in
canonical `test/feature/...` paths. Current audit: the root
`math_blocks_spec.md` still exists and is non-identical to the mirrored
`feature/usage` copy, so it remains an open duplicate-resolution item.

| Old path | New mirrored path |
|---|---|
| `doc/06_spec/math_blocks_spec.md` | `doc/06_spec/feature/usage/math_blocks_spec.md` (open duplicate; root still exists) |
| `doc/06_spec/remote_baremetal_library_spec.md` | `doc/06_spec/feature/app/remote_baremetal/remote_baremetal_library_spec.md` |
| `doc/06_spec/remote_baremetal_runtime_spec.md` | `doc/06_spec/feature/app/remote_baremetal/remote_baremetal_runtime_spec.md` |

### 2026-05-28 Batch 5

Moved the root syntax generated snapshot to the mirrored path declared by its
source spec, `test/feature/usage/syntax_spec.spl`. The older compiler feature
copy at `doc/06_spec/app/compiler/feature/usage/syntax_spec.md` is not
byte-for-byte identical, so it remains for a later comparison pass.

| Old path | New mirrored path |
|---|---|
| `doc/06_spec/syntax.md` | `doc/06_spec/feature/usage/syntax_spec.md` |

### 2026-05-28 Batch 6

Moved the web-dashboard app spec bucket from legacy `test/app/web_dashboard`
into the canonical feature/app tree. Existing root generated docs were moved to
the mirrored doc path, and concise scenario docs were added for the three
web-dashboard specs that had executable SPipe files but no mirrored generated
doc yet.

| Old path | New mirrored path |
|---|---|
| `test/app/web_dashboard/*` | `test/feature/app/web_dashboard/*` |
| `doc/06_spec/dashboard_render_spec.md` | `doc/06_spec/feature/app/web_dashboard/dashboard_render_spec.md` |
| `doc/06_spec/tmux_rest_api_spec.md` | `doc/06_spec/feature/app/web_dashboard/tmux_rest_api_spec.md` |
| - | `doc/06_spec/feature/app/web_dashboard/llm_agent_dashboard_spec.md` |
| - | `doc/06_spec/feature/app/web_dashboard/web_dashboard_html_shell_spec.md` |
| - | `doc/06_spec/feature/app/web_dashboard/web_dashboard_server_spec.md` |

### 2026-05-28 Batch 7

Moved the tmux stdlib unit spec from legacy `test/unit/lib/std/tmux` into the
canonical unit tree and moved the root generated doc to the mirrored path.

| Old path | New mirrored path |
|---|---|
| `test/unit/lib/std/tmux/*` | `test/unit/lib/std/tmux/*` |
| `doc/06_spec/tmux_api_spec.md` | `doc/06_spec/unit/lib/std/tmux/tmux_api_spec.md` |

### 2026-05-28 Batch 8

Replaced the root tensor-dimensions generated snapshot, which pointed to a
missing legacy `simple/std_lib/test/spec/...` source and contained zero tests,
with an executable SPipe traceability spec for the current tensor-dimension
source, design, guide, regenerator, and Lean artifact.

| Old path | New mirrored path |
|---|---|
| `doc/06_spec/tensor_dimensions.md` | `doc/06_spec/feature/ml/tensor_dimensions_spec.md` |
| - | `test/feature/ml/tensor_dimensions_spec.spl` |

### 2026-05-28 Batch 9

Moved the remaining legacy stdlib unit spec bucket from `test/lib/std/unit`
into `test/unit/lib/std`, preserving per-spec summary directories. The old
`test/lib/std` tree now only contains non-unit feature, integration, spec, and
type-checker buckets.

| Old path | New mirrored path |
|---|---|
| `test/lib/std/unit/*` | `test/unit/lib/std/*` |

### 2026-05-28 Batch 10

Cleared the remaining executable `test/lib/std` tree. Feature syntax coverage
now lives under `test/feature/language`, stdlib integration specs live under
`test/integration/lib/std`, spec-framework unit tests live under
`test/unit/lib/std/spec`, and executable type-checker coverage lives under
`test/unit/lib/std/type_checker`.

| Old path | New mirrored path |
|---|---|
| `test/lib/std/features/placeholder_lambda_spec.spl` | `test/feature/language/placeholder_lambda_spec.spl` |
| `test/lib/std/spec/decorators_spec.spl` | `test/unit/lib/std/spec/decorators_spec.spl` |
| `test/lib/std/type_checker/type_inference_spec.spl` | `test/unit/lib/std/type_checker/type_inference_spec.spl` |
| `test/lib/std/type_checker/type_inference_v2_spec.spl` | `test/unit/lib/std/type_checker/type_inference_v2_spec.spl` |
| `test/lib/std/integration/diagram/diagram_integration_spec.spl` | `test/integration/lib/std/diagram/diagram_integration_spec.spl` |
| `test/lib/std/integration/doctest/discovery_spec.spl` | `test/integration/lib/std/doctest/discovery_spec.spl` |
| `test/lib/std/integration/failsafe/crash_prevention_spec.spl` | `test/integration/lib/std/failsafe/crash_prevention_spec.spl` |
| `test/lib/std/integration/improvements/stdlib_improvements_spec.spl` | `test/integration/lib/std/improvements/stdlib_improvements_spec.spl` |
| `test/lib/std/integration/ml/simple_math_integration_spec.spl` | `test/integration/lib/std/ml/simple_math_integration_spec.spl` |
| `test/lib/std/integration/screenshot/screenshot_ffi_spec.spl` | `test/integration/lib/std/screenshot/screenshot_ffi_spec.spl` |

Follow-up: generated docs for placeholder lambda and decorators still have
older `test/feature/usage/...` source links in `doc/06_spec/app/compiler`.
Those files are non-identical legacy docs and should be regenerated or compared
instead of blindly moved.

### 2026-05-28 Batch 11

Removed the top-level smoke alias. The executable compile smoke spec now lives
with the existing system smoke suite, and the obsolete hidden `.sspec` wrapper
artifact was deleted.

| Old path | New mirrored path |
|---|---|
| `test/smoke/compile_smoke_spec.spl` | `test/system/smoke/compile_smoke_spec.spl` |
| `test/smoke/.sspec_wrapped_entry_compile_smoke_spec.spl` | deleted generated wrapper artifact |

### 2026-05-28 Batch 12

Removed the tracked temporary verifier-quality fixture roots. The integration
test now writes intentionally bad SPipe/source snippets under
`build/test-fixtures/verify_quality/...` and passes those paths directly into
the verifier, so broad `test/` discovery no longer sees deliberately failing
fixture specs.

| Old path | New mirrored path |
|---|---|
| `test/tmp_verify_quality/*` | generated at `build/test-fixtures/verify_quality/test/*` |
| `src/tmp_verify_quality/*` | generated at `build/test-fixtures/verify_quality/src/*` |

### 2026-05-28 Batch 13

Removed temporary scratch/spike roots. Green generic repro scripts became
scenario-based SPipe coverage under `test/feature/language/`. The failing
generic BTree spike was not left as active coverage; it is preserved as a repro
fixture with a bug note because it currently fails during parsing.

| Old path | New mirrored path |
|---|---|
| `test/scratch/repro_alias_method.spl` | `test/feature/language/generic_repro_spec.spl` |
| `test/scratch/repro_generic_method.spl` | `test/feature/language/generic_repro_spec.spl` |
| `test/scratch/repro_generic_static.spl` | tracked as parser-sensitive case in `doc/08_tracking/bug/generic_btree_spike_parse_dot.md` |
| `test/scratch/repro_patterns.spl` | partial green coverage in `test/feature/language/generic_repro_spec.spl`; multi-parameter generic constructor tracked in bug note |
| `test/spike/generic_btree_spike_spec.spl` | `test/fixtures/repro/language/generic_btree_spike_spec.spl.fixture` |

### 2026-05-28 Batch 14

Removed the `test/sys` alias in favor of canonical `test/system`. The
wm_compare suite moved as a unit with its checked-in PPM goldens, and the
SimpleOS driver/display system specs moved under `test/system/simpleos`.
Focused verification fixed stale matcher/import issues and exposed remaining
wm_compare behavioral failures tracked in
`doc/08_tracking/bug/wm_compare_system_specs_visible_failures.md`.

| Old path | New mirrored path |
|---|---|
| `test/sys/wm_compare/*` | `test/system/wm_compare/*` |
| `test/sys/simpleos_display_dma_contract_spec.spl` | `test/system/simpleos/display_dma_contract_spec.spl` |
| `test/sys/simpleos_driver_acceleration_perf_spec.spl` | `test/system/simpleos/driver_acceleration_perf_spec.spl` |
| - | `doc/06_spec/system/wm_compare/*_spec.md` |
| - | `doc/06_spec/system/simpleos/*_spec.md` |

### 2026-05-28 Batch 15

Removed the plural `test/features` alias. These files are Gherkin-style
feature-request fixtures, not executable SPipe specs, so they now live under the
support-data tree.

| Old path | New mirrored path |
|---|---|
| `test/features/*/*.feature` | `test/fixtures/feature_requests/*/*.feature` |

### 2026-05-28 Batch 16

Removed the top-level `test/bench` alias. Direct benchmark scripts now live
under the existing performance benchmark tree.

| Old path | New mirrored path |
|---|---|
| `test/bench/heavy_field_bench.spl` | `test/perf/bench/heavy_field_bench.spl` |
| `test/bench/method_dispatch_bench.spl` | `test/perf/bench/method_dispatch_bench.spl` |

### 2026-05-28 Batch 17

Removed small top-level utility aliases. Stats specs moved into the app stats
unit bucket; lint and repro scripts moved under fixture/support trees so broad
test discovery does not treat them as canonical executable suites.

| Old path | New mirrored path |
|---|---|
| `test/stats/*_spec.spl` | `test/unit/app/stats/*_spec.spl` |
| `test/lint/param_tag_test_fixture.spl` | `test/fixtures/lint/param_tag_test_fixture.spl` |
| `test/util/game2d_*.spl` | `test/fixtures/repro/game2d/game2d_*.spl` |
| `test/util/hir_any_field_repro.spl` | `test/fixtures/repro/compiler/hir/hir_any_field_repro.spl` |

### 2026-05-28 Batch 18

Removed the top-level `test/code_quality` domain root. These specs are
system-level quality gates and canaries, so they now live under
`test/system/code_quality`.

| Old path | New mirrored path |
|---|---|
| `test/code_quality/*_spec.spl` | `test/system/code_quality/*_spec.spl` |

Removed the top-level `test/data` support root. The only tracked file was an
agent roundtrip fixture, now under `test/fixtures/data/agents/`.

| Old path | New mirrored path |
|---|---|
| `test/data/agents/test_roundtrip_001.txt` | `test/fixtures/data/agents/test_roundtrip_001.txt` |

`test/shared` was inspected during the next slice and is now kept as the
canonical executable cross-platform tier for `# @platform: all` SPipe specs.
It is not a fixture bucket and should not be moved to `test/unit/shared`.

| Option | Consequence |
|---|---|
| Keep `test/shared` | Done; single-file and directory runs now discover and execute these specs. |
| Move to `test/unit/shared` | Rejected; this would contradict the platform-tier guide and existing evidence layout. |

### 2026-05-28 Batch 19

Resolved the only imported spec in `test/shared`. The contract testing helper
coverage imports `lib.common.contract` and exercises mock-server/provider/broker
surfaces, so it is unit coverage for `lib/common/contracts`, not shared/core
cross-platform coverage. The shared guide now explicitly allows the built-in
`context` BDD helper used by otherwise import-free shared specs.

| Old path | New mirrored path |
|---|---|
| `test/shared/types/contract_spec.spl` | `test/unit/lib/common/contracts/contract_testing_spec.spl` |
| `test/shared/types/contract/summary.txt` | `test/unit/lib/common/contracts/contract/summary.txt` |
| - | `doc/06_spec/unit/lib/common/contracts/contract_testing_spec.md` |

## Root-Level Files

| File | Likely owner | Canonical target | Safe next move |
|---|---|---|---|
| `doc/06_spec/INDEX.md` | Global doc index | keep root | Keep; update after migration tooling is stable. |
| `doc/06_spec/README.md` | Global layout guide | keep root | Keep; already documents canonical layout. |
| `doc/06_spec/feature/language/async_default_spec.md` | `test/feature/language/async_default_spec.spl` | `doc/06_spec/feature/language/async_default_spec.md` or `doc/06_spec/feature/compiler/async_default_spec.md` | Confirm whether `test/feature/language` migrates to `test/feature/compiler`; then regenerate. |
| `doc/06_spec/bootstrap_test_gate.sdn` | `doc/02_requirements/feature/remote_jit_exec_hardening.sdn` | data owner TBD | Leave in place until SDN consumer is found. |
| `doc/06_spec/feature/language/capability_effects_spec.md` | `test/feature/language/capability_effects_spec.spl` | `doc/06_spec/feature/language/capability_effects_spec.md` | Confirm `test/feature/language` destination; regenerate. |
| `doc/06_spec/ch32v307_composite_runner_path_spec.md` | `test/integration/remote_jit/ch32v307_composite_runner_path_spec.spl` | `doc/06_spec/integration/remote_jit/ch32v307_composite_runner_path_spec.md` | Done in Batch 1. |
| `doc/06_spec/feature/language/concurrency_spec.md` | `test/feature/language/concurrency_spec.spl` | `doc/06_spec/feature/language/concurrency_spec.md` | Confirm `test/feature/language` destination; regenerate. |
| `doc/06_spec/feature/app/web_dashboard/dashboard_render_spec.md` | `test/feature/app/web_dashboard/dashboard_render_spec.spl` | `doc/06_spec/feature/app/web_dashboard/dashboard_render_spec.md` | Done in Batch 6. |
| `doc/06_spec/feature/language/data_structures_spec.md` | `test/feature/language/data_structures_spec.spl` | `doc/06_spec/feature/language/data_structures_spec.md` | Confirm `test/feature/language` destination; regenerate. |
| `doc/06_spec/feature.md` | Feature category inventory | generated/catalog TBD | Do not move until inventory generator ownership is known. |
| `doc/06_spec/feature_db.sdn` | `test/unit/app/tooling/feature_db_spec.spl` plus stats tooling | data owner TBD | Leave in place; document consumer before moving. |
| `doc/06_spec/feature/language/functions_spec.md` | `test/feature/language/functions_spec.spl` | `doc/06_spec/feature/language/functions_spec.md` | Confirm `test/feature/language` destination; regenerate. |
| `doc/06_spec/loss_nograd_blocks_spec.md` | `test/feature/usage/loss_nograd_blocks_spec.spl` | `doc/06_spec/feature/usage/loss_nograd_blocks_spec.md` | Safe root cleanup after regenerating/updating canonical mirrored doc; audit found only the `Updated` date differs from the mirrored copy. |
| `doc/06_spec/feature/language/macro_spec.md` | `test/feature/language/macro_spec.spl` | `doc/06_spec/feature/language/macro_spec.md` | Confirm `test/feature/language` destination; regenerate. |
| `doc/06_spec/feature/usage/math_blocks_spec.md` | `test/feature/usage/math_blocks_spec.spl`; root duplicate still exists | `doc/06_spec/feature/usage/math_blocks_spec.md` | Safe root cleanup after canonical regeneration; keep the richer mirrored doc, not the shorter root scenario list. |
| `doc/06_spec/math_render_spec.md` | `test/feature/usage/math_render_spec.spl` | `doc/06_spec/feature/usage/math_render_spec.md` | Safe root cleanup after regenerating/updating canonical mirrored doc; audit found only the `Updated` date differs from the mirrored copy. |
| `doc/06_spec/feature/language/memory_spec.md` | `test/feature/language/memory_spec.spl` | `doc/06_spec/feature/language/memory_spec.md` | Confirm `test/feature/language` destination; regenerate. |
| `doc/06_spec/metaprogramming.md` | `test/feature/usage/metaprogramming_spec.spl`; also `test/feature/language/macro_spec.spl` hints | `doc/06_spec/feature/usage/metaprogramming_spec.md` | Done in Batch 3; macro overlap remains a later comparison task. |
| `doc/06_spec/feature/language/modules_spec.md` | `test/feature/language/modules_spec.spl` | `doc/06_spec/feature/language/modules_spec.md` | Confirm `test/feature/language` destination; regenerate. |
| `doc/06_spec/pending_feature.md` | Feature inventory/stats tooling | generated/catalog TBD | Leave until generator and destination catalog are defined. |
| `doc/06_spec/qemu_rv32_raw_injected_regression_spec.md` | `test/integration/remote_jit/qemu_rv32_raw_injected_regression_spec.spl` | `doc/06_spec/integration/remote_jit/qemu_rv32_raw_injected_regression_spec.md` | Done in Batch 1. |
| `doc/06_spec/feature/app/remote_baremetal/remote_baremetal_library_spec.md` | `test/feature/app/remote_baremetal/remote_baremetal_library_spec.spl` | `doc/06_spec/feature/app/remote_baremetal/remote_baremetal_library_spec.md` | Done in Batch 4. |
| `doc/06_spec/feature/app/remote_baremetal/remote_baremetal_runtime_spec.md` | `test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl` | `doc/06_spec/feature/app/remote_baremetal/remote_baremetal_runtime_spec.md` | Done in Batch 4. |
| `doc/06_spec/sandboxing.md` | `test/feature/usage/sandboxing_spec.spl` | `doc/06_spec/feature/usage/sandboxing_spec.md` | Done in Batch 3. |
| `doc/06_spec/shell_api.md` | `test/feature/app/shell_api_spec.spl` | `doc/06_spec/feature/app/shell_api_spec.md` | Done in Batch 3. |
| `doc/06_spec/feature/language/suspension_operator_spec.md` | `test/feature/language/suspension_operator_spec.spl` | duplicate of `_spec` markdown | Compare with `suspension_operator_spec.md`, then delete or redirect duplicate. |
| `doc/06_spec/suspension_operator_spec.md` | `test/feature/language/suspension_operator_spec.spl` | `doc/06_spec/feature/language/suspension_operator_spec.md` | Confirm `test/feature/language` destination; regenerate. |
| `doc/06_spec/feature/usage/syntax_spec.md` | `test/feature/usage/syntax_spec.spl`; older non-identical compiler copy also exists under `app/compiler/feature/usage` | `doc/06_spec/feature/usage/syntax_spec.md` | Done in Batch 5; compare older compiler copy later. |
| `doc/06_spec/feature/ml/tensor_dimensions_spec.md` | `test/feature/ml/tensor_dimensions_spec.spl` | `doc/06_spec/feature/ml/tensor_dimensions_spec.md` | Done in Batch 8. |
| `doc/06_spec/unit/lib/std/tmux/tmux_api_spec.md` | `test/unit/lib/std/tmux/tmux_api_spec.spl` | `doc/06_spec/unit/lib/std/tmux/tmux_api_spec.md` | Done in Batch 7. |
| `doc/06_spec/feature/app/web_dashboard/tmux_rest_api_spec.md` | `test/feature/app/web_dashboard/tmux_rest_api_spec.spl` | `doc/06_spec/feature/app/web_dashboard/tmux_rest_api_spec.md` | Done in Batch 6. |
| `doc/06_spec/feature/language/traits_spec.md` | `test/feature/language/traits_spec.spl` | `doc/06_spec/feature/language/traits_spec.md` | Confirm `test/feature/language` destination; regenerate. |
| `doc/06_spec/feature/language/type_inference_spec.md` | `test/feature/language/type_inference_spec.spl` | `doc/06_spec/feature/language/type_inference_spec.md` | Confirm `test/feature/language` destination; regenerate. |
| `doc/06_spec/types.md` | `test/feature/usage/types_spec.spl` | `doc/06_spec/feature/usage/types_spec.md` | Done in Batch 3; broader type-system duplicate docs remain for later comparison. |

## Legacy And Runtime Files

| File | Likely owner | Canonical target | Safe next move |
|---|---|---|---|
| `doc/06_spec/legacy/INDEX.md` | Legacy navigation | delete after legacy bucket empties | Stale; safe to delete after the TRACE32 legacy doc is migrated. |
| `doc/06_spec/legacy/command_dispatch_spec.md` | `test/unit/app/tooling/command_dispatch_spec.spl` | `doc/06_spec/unit/app/tooling/command_dispatch_spec.md` | Done in Batch 1. |
| `doc/06_spec/legacy/test-spec.html` | Old docgen fixture/output | archive/delete candidate | Exact-path search found only migration-map references; safe after doc-nav fixture confirmation. |
| `doc/06_spec/legacy/test-spec.md` | Old docgen fixture/output | archive/delete candidate | Exact-path search found only migration-map references; safe after doc-nav fixture confirmation. |
| `doc/06_spec/legacy/test_runner_simple_spec.md` | `test/unit/app/tooling/test_runner_simple_spec.spl` | `doc/06_spec/unit/app/tooling/test_runner_simple_spec.md` | Done in Batch 1. |
| `doc/06_spec/legacy/trace32_stm32h7_jit_e2e_spec.md` | `test/feature/app/remote_jit/trace32_stm32h7_jit_e2e_spec.spl` | `doc/06_spec/feature/app/remote_jit/trace32_stm32h7_jit_e2e_spec.md` | Regenerate from feature spec. |
| `doc/06_spec/runtime/rt_gui_glass_contract.md` | Runtime GUI manual contract; no direct source spec found | `doc/06_spec/runtime/gui/rt_gui_glass_contract.md` or design doc | Manual review; add source spec if this remains a release contract. |

## Safe Next Moves

1. Add or update docgen support to write mirrored destinations from source
   `test/..._spec.spl` paths, including unit/integration/feature paths.
2. Regenerate the high-confidence one-to-one files first:
   remote JIT integration specs, remote baremetal feature specs, shell API,
   sandboxing, math render, loss/nograd, command dispatch, test runner simple.
3. Leave SDN/catalog files in place until their producers and consumers are
   explicitly traced.
4. After a small migration batch, run traceability checks and doc navigation
   tests before moving the next batch.
5. Broader test-layout candidates identified by sidecar review: top-level
   temporary/experimental roots (`test/tmp_verify_quality`, `test/scratch`,
   `test/spike`), duplicate category aliases (`test/features`, `test/sys`,
   `test/smoke`), and domain-first roots (`test/app`, `test/compiler`,
   `test/browser_engine`, `test/code_quality`, `test/dbfs`, `test/hal`,
   `test/js`, `test/kernel`, `test/nvfs`, `test/os`, `test/qemu`,
   `test/reftest`, `test/riscv64_fpga`, `test/rtl`, `test/runtime`,
   `test/sffi`, `test/tools`, `test/web_platform`). Treat these as separate
   batches because CI and baseline paths may call them directly. `test/shared`
   is now resolved as a canonical cross-platform runner tier, not a fixture
   cleanup; its known imported contract spec has moved to the unit contract
   helper bucket.
