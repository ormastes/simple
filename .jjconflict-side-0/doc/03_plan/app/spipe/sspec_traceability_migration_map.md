# SPipe Traceability Migration Map

Date: 2026-05-28

Scope: planning and restart map for the former `sspec` documentation/test
layout. `sspec` is obsolete; use SPipe names for new work. Do not move files
from this map until the source SPipe owner is confirmed and the generated
markdown path can be regenerated or moved without losing traceability metadata.

## Status

**Map current; broad root migration complete.** This map now reflects the
current tree, including completed batches and remaining catalog/manual-doc
follow-ups. No current top-level executable `test/` roots are known to need
policy migration; keep the remaining `doc/06_spec` catalog/data items in place
until their producers and consumers are traced.

Current root/legacy audit from the worktree:

| Area | Current state | Required action |
|---|---|---|
| Root navigation | `doc/06_spec/INDEX.md`, `doc/06_spec/README.md` | Keep at root. |
| Root data/catalog | `bootstrap_test_gate.sdn`, `feature.md`, `feature_db.sdn`, `pending_feature.md` | Trace producers/consumers before moving. |
| Root generated math docs | none | Resolved in Batch 20; canonical docs live under `doc/06_spec/feature/usage/`. |
| Legacy generated index | none | Resolved in Batch 21. |
| Legacy live TRACE32 doc | none | Resolved in Batch 21. |
| Runtime manual contract | `runtime/rt_gui_glass_contract.md` | Decide whether it is a manual runtime contract or needs an executable source spec. |
| Generated/category folders | `generated/pending_feature.md`, `categories/*.md`, `diagrams/.gitkeep` | Leave until generator ownership is traced. |

Current `test/` top-level roots still needing policy/migration review: none
known from the current audit.
The low-risk `test/hal`, `test/rtl`, `test/runtime`, `test/sffi`, and shallow
`test/compiler` slices are resolved in Batches 22 and 23. `test/kernel` is
resolved in Batch 24. `test/fuzz` is resolved in Batch 25. `test/js` is
resolved in Batch 26. `test/nvfs` is resolved in Batch 27. `test/tools` is
resolved in Batch 28. `test/dbfs` is resolved in Batch 29.
`test/browser_engine`, `test/web_platform`, and `test/reftest` are resolved in
Batch 30. `test/qemu` and `test/riscv64_fpga` are resolved in Batch 31.
`test/app` is resolved in Batch 32. `test/os` is resolved in Batch 33.
`test/lib` is resolved in Batch 34.
`test/baselines`, `test/fixtures`, `test/perf`, `test/shared`,
`test/system`, `test/unit`, `test/integration`, and `test/feature` already
have an explicit role.

## Current Shape

- Canonical spec docs mostly live under mirrored subtrees, but legacy
  `doc/06_spec/app/compiler/...` docs still coexist with newer
  `doc/06_spec/feature/...`, `unit/...`, `integration/...`, and `system/...`
  docs.
- Root-level `doc/06_spec` currently has six files: two navigation docs and
  four catalog/data files. Generated spec docs should live under mirrored
  subtrees, not the root.
- Additional non-mirrored bucket: `doc/06_spec/runtime/rt_gui_glass_contract.md`.
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
path was known and whose mirrored target did not already exist. Root math
duplicates from this batch were later resolved in Batch 20.

| Old path | New mirrored path |
|---|---|
| `doc/06_spec/loss_nograd_blocks_spec.md` | `doc/06_spec/feature/usage/loss_nograd_blocks_spec.md` (root duplicate removed in Batch 20) |
| `doc/06_spec/math_render_spec.md` | `doc/06_spec/feature/usage/math_render_spec.md` (root duplicate removed in Batch 20) |
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
moved to `test/03_system/feature/language/`; root language docs moved to
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
canonical `test/03_system/feature/...` paths. The remaining root
`math_blocks_spec.md` duplicate was later resolved in Batch 20 by keeping the
richer mirrored `feature/usage` copy.

| Old path | New mirrored path |
|---|---|
| `doc/06_spec/math_blocks_spec.md` | `doc/06_spec/feature/usage/math_blocks_spec.md` (root duplicate removed in Batch 20) |
| `doc/06_spec/remote_baremetal_library_spec.md` | `doc/06_spec/feature/app/remote_baremetal/remote_baremetal_library_spec.md` |
| `doc/06_spec/remote_baremetal_runtime_spec.md` | `doc/06_spec/feature/app/remote_baremetal/remote_baremetal_runtime_spec.md` |

### 2026-05-28 Batch 5

Moved the root syntax generated snapshot to the mirrored path declared by its
source spec, `test/03_system/feature/usage/syntax_spec.spl`. The older compiler feature
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
| `test/app/web_dashboard/*` | `test/03_system/feature/app/web_dashboard/*` |
| `doc/06_spec/dashboard_render_spec.md` | `doc/06_spec/feature/app/web_dashboard/dashboard_render_spec.md` |
| `doc/06_spec/tmux_rest_api_spec.md` | `doc/06_spec/feature/app/web_dashboard/tmux_rest_api_spec.md` |
| - | `doc/06_spec/feature/app/web_dashboard/llm_agent_dashboard_spec.md` |
| - | `doc/06_spec/feature/app/web_dashboard/web_dashboard_html_shell_spec.md` |
| - | `doc/06_spec/feature/app/web_dashboard/web_dashboard_server_spec.md` |

### 2026-05-28 Batch 7

Moved the tmux stdlib unit spec from legacy `test/01_unit/lib/std/tmux` into the
canonical unit tree and moved the root generated doc to the mirrored path.

| Old path | New mirrored path |
|---|---|
| `test/01_unit/lib/std/tmux/*` | `test/01_unit/lib/std/tmux/*` |
| `doc/06_spec/tmux_api_spec.md` | `doc/06_spec/unit/lib/std/tmux/tmux_api_spec.md` |

### 2026-05-28 Batch 8

Replaced the root tensor-dimensions generated snapshot, which pointed to a
missing legacy `simple/std_lib/test/spec/...` source and contained zero tests,
with an executable SPipe traceability spec for the current tensor-dimension
source, design, guide, regenerator, and Lean artifact.

| Old path | New mirrored path |
|---|---|
| `doc/06_spec/tensor_dimensions.md` | `doc/06_spec/feature/ml/tensor_dimensions_spec.md` |
| - | `test/03_system/feature/ml/tensor_dimensions_spec.spl` |

### 2026-05-28 Batch 9

Moved the remaining legacy stdlib unit spec bucket from `test/lib/std/unit`
into `test/01_unit/lib/std`, preserving per-spec summary directories. The old
`test/lib/std` tree now only contains non-unit feature, integration, spec, and
type-checker buckets.

| Old path | New mirrored path |
|---|---|
| `test/lib/std/unit/*` | `test/01_unit/lib/std/*` |

### 2026-05-28 Batch 10

Cleared the remaining executable `test/lib/std` tree. Feature syntax coverage
now lives under `test/03_system/feature/language`, stdlib integration specs live under
`test/02_integration/lib/std`, spec-framework unit tests live under
`test/01_unit/lib/std/spec`, and executable type-checker coverage lives under
`test/01_unit/lib/std/type_checker`.

| Old path | New mirrored path |
|---|---|
| `test/lib/std/features/placeholder_lambda_spec.spl` | `test/03_system/feature/language/placeholder_lambda_spec.spl` |
| `test/lib/std/spec/decorators_spec.spl` | `test/01_unit/lib/std/spec/decorators_spec.spl` |
| `test/lib/std/type_checker/type_inference_spec.spl` | `test/01_unit/lib/std/type_checker/type_inference_spec.spl` |
| `test/lib/std/type_checker/type_inference_v2_spec.spl` | `test/01_unit/lib/std/type_checker/type_inference_v2_spec.spl` |
| `test/lib/std/integration/diagram/diagram_integration_spec.spl` | `test/02_integration/lib/std/diagram/diagram_integration_spec.spl` |
| `test/lib/std/integration/doctest/discovery_spec.spl` | `test/02_integration/lib/std/doctest/discovery_spec.spl` |
| `test/lib/std/integration/failsafe/crash_prevention_spec.spl` | `test/02_integration/lib/std/failsafe/crash_prevention_spec.spl` |
| `test/lib/std/integration/improvements/stdlib_improvements_spec.spl` | `test/02_integration/lib/std/improvements/stdlib_improvements_spec.spl` |
| `test/lib/std/integration/ml/simple_math_integration_spec.spl` | `test/02_integration/lib/std/ml/simple_math_integration_spec.spl` |
| `test/lib/std/integration/screenshot/screenshot_ffi_spec.spl` | `test/02_integration/lib/std/screenshot/screenshot_ffi_spec.spl` |

Follow-up: generated docs for placeholder lambda and decorators still have
older `test/03_system/feature/usage/...` source links in `doc/06_spec/app/compiler`.
Those files are non-identical legacy docs and should be regenerated or compared
instead of blindly moved.

### 2026-05-28 Batch 11

Removed the top-level smoke alias. The executable compile smoke spec now lives
with the existing system smoke suite, and the obsolete hidden `.sspec` wrapper
artifact was deleted.

| Old path | New mirrored path |
|---|---|
| `test/04_smoke/compile_smoke_spec.spl` | `test/03_system/smoke/compile_smoke_spec.spl` |
| `test/04_smoke/.sspec_wrapped_entry_compile_smoke_spec.spl` | deleted generated wrapper artifact |

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
scenario-based SPipe coverage under `test/03_system/feature/language/`. The failing
generic BTree spike was not left as active coverage; it is preserved as a repro
fixture with a bug note because it currently fails during parsing.

| Old path | New mirrored path |
|---|---|
| `test/scratch/repro_alias_method.spl` | `test/03_system/feature/language/generic_repro_spec.spl` |
| `test/scratch/repro_generic_method.spl` | `test/03_system/feature/language/generic_repro_spec.spl` |
| `test/scratch/repro_generic_static.spl` | tracked as parser-sensitive case in `doc/08_tracking/bug/generic_btree_spike_parse_dot.md` |
| `test/scratch/repro_patterns.spl` | partial green coverage in `test/03_system/feature/language/generic_repro_spec.spl`; multi-parameter generic constructor tracked in bug note |
| `test/spike/generic_btree_spike_spec.spl` | `test/fixtures/repro/language/generic_btree_spike_spec.spl.fixture` |

### 2026-05-28 Batch 14

Removed the `test/sys` alias in favor of canonical `test/system`. The
wm_compare suite moved as a unit with its checked-in PPM goldens, and the
SimpleOS driver/display system specs moved under `test/03_system/simpleos`.
Focused verification fixed stale matcher/import issues and exposed remaining
wm_compare behavioral failures tracked in
`doc/08_tracking/bug/wm_compare_system_specs_visible_failures.md`.

| Old path | New mirrored path |
|---|---|
| `test/sys/wm_compare/*` | `test/03_system/wm_compare/*` |
| `test/sys/simpleos_display_dma_contract_spec.spl` | `test/03_system/simpleos/display_dma_contract_spec.spl` |
| `test/sys/simpleos_driver_acceleration_perf_spec.spl` | `test/03_system/simpleos/driver_acceleration_perf_spec.spl` |
| - | `doc/06_spec/system/wm_compare/*_spec.md` |
| - | `doc/06_spec/system/simpleos/*_spec.md` |

### 2026-05-28 Batch 15

Removed the plural `test/features` alias. These files are Gherkin-style
feature-request fixtures, not executable SPipe specs, so they now live under the
support-data tree.

| Old path | New mirrored path |
|---|---|
| `test/features/*/*.feature` | `test/fixtures/features/*/*.feature` |

### 2026-05-28 Batch 16

Removed the top-level `test/bench` alias. Direct benchmark scripts now live
under the existing performance benchmark tree.

| Old path | New mirrored path |
|---|---|
| `test/bench/heavy_field_bench.spl` | `test/05_perf/bench/heavy_field_bench.spl` |
| `test/bench/method_dispatch_bench.spl` | `test/05_perf/bench/method_dispatch_bench.spl` |

### 2026-05-28 Batch 17

Removed small top-level utility aliases. Stats specs moved into the app stats
unit bucket; lint and repro scripts moved under fixture/support trees so broad
test discovery does not treat them as canonical executable suites.

| Old path | New mirrored path |
|---|---|
| `test/stats/*_spec.spl` | `test/01_unit/app/stats/*_spec.spl` |
| `test/lint/param_tag_test_fixture.spl` | `test/fixtures/lint/param_tag_test_fixture.spl` |
| `test/util/game2d_*.spl` | `test/fixtures/repro/game2d/game2d_*.spl` |
| `test/util/hir_any_field_repro.spl` | `test/fixtures/repro/compiler/hir/hir_any_field_repro.spl` |

### 2026-05-28 Batch 18

Removed the top-level `test/code_quality` domain root. These specs are
system-level quality gates and canaries, so they now live under
`test/03_system/code_quality`.

| Old path | New mirrored path |
|---|---|
| `test/code_quality/*_spec.spl` | `test/03_system/code_quality/*_spec.spl` |

Removed the top-level `test/data` support root. The only tracked file was an
agent roundtrip fixture, now under `test/fixtures/data/agents/`.

| Old path | New mirrored path |
|---|---|
| `test/data/agents/test_roundtrip_001.txt` | `test/fixtures/data/agents/test_roundtrip_001.txt` |

`test/shared` was inspected during the next slice and is now kept as the
canonical executable cross-platform tier for `# @platform: all` SPipe specs.
It is not a fixture bucket and should not be moved to `test/01_unit/shared`.

| Option | Consequence |
|---|---|
| Keep `test/shared` | Done; single-file and directory runs now discover and execute these specs. |
| Move to `test/01_unit/shared` | Rejected; this would contradict the platform-tier guide and existing evidence layout. |

### 2026-05-28 Batch 19

Resolved the only imported spec in `test/shared`. The contract testing helper
coverage imports `lib.common.contract` and exercises mock-server/provider/broker
surfaces, so it is unit coverage for `lib/common/contracts`, not shared/core
cross-platform coverage. The shared guide now explicitly allows the built-in
`context` BDD helper used by otherwise import-free shared specs.

| Old path | New mirrored path |
|---|---|
| `test/shared/types/contract_spec.spl` | `test/01_unit/lib/common/contracts/contract_testing_spec.spl` |
| `test/shared/types/contract/summary.txt` | `test/01_unit/lib/common/contracts/contract/summary.txt` |
| - | `doc/06_spec/unit/lib/common/contracts/contract_testing_spec.md` |

### 2026-05-28 Batch 20

Removed the remaining root-level generated math duplicates after confirming
their mirrored `feature/usage` owners. `loss_nograd_blocks_spec.md` and
`math_render_spec.md` differed from their mirrored copies only by the Updated
date; the mirrored `math_blocks_spec.md` was richer than the shorter root
scenario-list snapshot, so the mirrored file was kept.

| Old path | New mirrored path |
|---|---|
| `doc/06_spec/loss_nograd_blocks_spec.md` | `doc/06_spec/feature/usage/loss_nograd_blocks_spec.md` |
| `doc/06_spec/math_render_spec.md` | `doc/06_spec/feature/usage/math_render_spec.md` |
| `doc/06_spec/math_blocks_spec.md` | `doc/06_spec/feature/usage/math_blocks_spec.md` |

### 2026-05-28 Batch 21

Cleared the legacy generated-doc bucket. The only live generated spec in the
legacy bucket, TRACE32 STM32H7 JIT E2E, moved to the mirrored feature/app path.
The old `test-spec` markdown/HTML outputs and the legacy bucket index were
deleted after exact-path search found no consumers outside this migration map.

| Old path | New mirrored path |
|---|---|
| `doc/06_spec/legacy/trace32_stm32h7_jit_e2e_spec.md` | `doc/06_spec/feature/app/remote_jit/trace32_stm32h7_jit_e2e_spec.md` |
| `doc/06_spec/legacy/INDEX.md` | deleted stale legacy navigation |
| `doc/06_spec/legacy/test-spec.md` | deleted stale generated output |
| `doc/06_spec/legacy/test-spec.html` | deleted stale generated output |

### 2026-05-28 Batch 22

Moved low-risk unit/API roots into canonical unit and fixture buckets.
Focused discovery works at the new paths, but several migrated tests expose
pre-existing or now-visible failures under interpreter verification.

| Old path | New mirrored path |
|---|---|
| `test/hal/hal_traits_spec.spl` | `test/01_unit/hal/hal_traits_spec.spl` |
| `test/rtl/encode_riscv_spec.spl` | `test/01_unit/rtl/encode_riscv_spec.spl` |
| `test/sffi/sffi_public_api_spec.spl` | `test/01_unit/sffi/sffi_public_api_spec.spl` |
| `test/runtime/simd_text_test.spl` | `test/01_unit/runtime/simd_text/simd_text_test.spl` |
| `test/runtime/simd_text_fuzz_test.spl` | `test/01_unit/runtime/simd_text/simd_text_fuzz_test.spl` |
| `test/runtime/simd_text_fuzz.spl` | `test/fixtures/runtime/simd_text/simd_text_fuzz.spl` |

Verification summary: `test/01_unit/hal/hal_traits_spec.spl` passed 30/30.
`test/01_unit/rtl/encode_riscv_spec.spl`, `test/01_unit/sffi/sffi_public_api_spec.spl`,
and the two runtime SIMD text specs were discovered at their new paths but did
not pass focused interpreter verification.

### 2026-05-28 Batch 23

Moved the current shallow `test/compiler` slice into canonical compiler unit
buckets. The move intentionally overwrote older same-name
`test/01_unit/compiler/mir_opt/{bounds_check_elim,copy_propagation}_spec.spl`
files with the active top-level versions, matching the migration worker result.

| Old path | New mirrored path |
|---|---|
| `test/compiler/auto_vec_string_test.spl` | `test/01_unit/compiler/semantics/auto_vec_string_test.spl` |
| `test/compiler/mir_opt/bounds_check_elim_spec.spl` | `test/01_unit/compiler/mir_opt/bounds_check_elim_spec.spl` |
| `test/compiler/mir_opt/clib_parity_hotspot_spec.spl` | `test/01_unit/compiler/mir_opt/clib_parity_hotspot_spec.spl` |
| `test/compiler/mir_opt/copy_propagation_spec.spl` | `test/01_unit/compiler/mir_opt/copy_propagation_spec.spl` |
| `test/compiler/mir_opt/loop_invariant_motion_spec.spl` | `test/01_unit/compiler/mir_opt/loop_invariant_motion_spec.spl` |
| `test/compiler/mir_opt/pattern_rule_spec.spl` | `test/01_unit/compiler/mir_opt/pattern_rule_spec.spl` |
| `test/compiler/mir_opt/typed_byte_canon_spec.spl` | `test/01_unit/compiler/mir_opt/typed_byte_canon_spec.spl` |
| `test/compiler/vhdl/hardware_spawn_lower_spec.spl` | `test/01_unit/compiler/vhdl/hardware_spawn_lower_spec.spl` |

Verification summary: auto-vector string and the six MIR optimization specs
passed focused interpreter runs. `test/01_unit/compiler/vhdl/hardware_spawn_lower_spec.spl`
is discovered at its new path but currently fails 17 examples with semantic
errors such as missing `kind`, `label_count`, and `is_output` variables.

### 2026-05-28 Batch 24

Moved the top-level kernel boot/loader specs into the canonical system kernel
bucket. These specs exercise boot filesystem, ELF loading, and NVFS-backed ELF
load chains against OS/kernel modules rather than isolated unit helpers, so
`test/03_system/kernel` is the conservative target.

| Old path | New mirrored path |
|---|---|
| `test/kernel/boot_fs_mount_spec.spl` | `test/03_system/kernel/boot_fs_mount_spec.spl` |
| `test/kernel/boot_fs_spec.spl` | `test/03_system/kernel/boot_fs_spec.spl` |
| `test/kernel/elf_load_chain_spec.spl` | `test/03_system/kernel/elf_load_chain_spec.spl` |
| `test/kernel/nvfs_elf_load_spec.spl` | `test/03_system/kernel/nvfs_elf_load_spec.spl` |

Verification:

- `SIMPLE_LIB=src bin/simple test --force-rebuild test/03_system/kernel/boot_fs_mount_spec.spl` passed 8/8.
- `SIMPLE_LIB=src bin/simple test --force-rebuild test/03_system/kernel/boot_fs_spec.spl` passed 11/11.
- `SIMPLE_LIB=src bin/simple test --force-rebuild test/03_system/kernel/elf_load_chain_spec.spl` passed 6/6.
- `SIMPLE_LIB=src bin/simple test --force-rebuild test/03_system/kernel/nvfs_elf_load_spec.spl` passed 3/3.

### 2026-05-28 Batch 25

Moved deterministic fuzz/property specs into the canonical language feature
fuzz bucket. These specs exercise language primitives and parser/text/string
behavior, not a multi-component system workflow, so `test/03_system/feature/language/fuzz`
is the conservative target. Summary evidence directories moved with their
specs.

| Old path | New mirrored path |
|---|---|
| `test/06_fuzz/numeric_robustness_fuzz_spec.spl` | `test/03_system/feature/language/fuzz/numeric_robustness_fuzz_spec.spl` |
| `test/06_fuzz/numeric_robustness_fuzz/summary.txt` | `test/03_system/feature/language/fuzz/numeric_robustness_fuzz/summary.txt` |
| `test/06_fuzz/parser_roundtrip_fuzz_spec.spl` | `test/03_system/feature/language/fuzz/parser_roundtrip_fuzz_spec.spl` |
| `test/06_fuzz/parser_roundtrip_fuzz/summary.txt` | `test/03_system/feature/language/fuzz/parser_roundtrip_fuzz/summary.txt` |
| `test/06_fuzz/string_operations_fuzz_spec.spl` | `test/03_system/feature/language/fuzz/string_operations_fuzz_spec.spl` |
| `test/06_fuzz/string_operations_fuzz/summary.txt` | `test/03_system/feature/language/fuzz/string_operations_fuzz/summary.txt` |

Verification: `bin/simple test test/03_system/feature/language/fuzz --mode=interpreter --no-cache`
passed 33/33 across three files.

### 2026-05-28 Batch 26

Moved JS executable conformance specs to the canonical feature bucket and moved
the shell compatibility harness to fixtures. The Simple spec files are
byte-for-byte identical to their old top-level contents; the move exposes the
same JS conformance failures at the new path.

| Old path | New mirrored path |
|---|---|
| `test/js/es5_conformance_spec.spl` | `test/03_system/feature/js/es5_conformance_spec.spl` |
| `test/js/es2015_conformance_spec.spl` | `test/03_system/feature/js/es2015_conformance_spec.spl` |
| `test/js/node_api_conformance_spec.spl` | `test/03_system/feature/js/node_api_conformance_spec.spl` |
| `test/js/interpreter_vars_spec.spl` | `test/03_system/feature/js/interpreter_vars_spec.spl` |
| `test/js/compat_test.sh` | `test/fixtures/js/compat_test.sh` |

Verification: `bash -n test/fixtures/js/compat_test.sh` passed.
`bin/simple test test/03_system/feature/js` discovered all four moved specs but failed
existing JS conformance coverage with 0 passed and 114 failed. Focused
`--fail-fast` checks also failed for `node_api_conformance_spec.spl` and
`es5_conformance_spec.spl`. The full shell harness hung inside
`bin/simple run src/app/js/main.spl -e ...` and was terminated by the worker.

### 2026-05-28 Batch 27

Moved NVFS host-side driver and persistence specs into the canonical storage
integration bucket. These specs exercise NVFS arenas, POSIX wrapper behavior,
superblock disk I/O, and remount persistence against a block-device-backed
fixture, so `test/02_integration/storage/nvfs` is the conservative target.

| Old path | New mirrored path |
|---|---|
| `test/nvfs/nvfs_name_persistence_spec.spl` | `test/02_integration/storage/nvfs/nvfs_name_persistence_spec.spl` |
| `test/nvfs/nvfs_nvme_arena_spec.spl` | `test/02_integration/storage/nvfs/nvfs_nvme_arena_spec.spl` |
| `test/nvfs/nvfs_posix_nvme_spec.spl` | `test/02_integration/storage/nvfs/nvfs_posix_nvme_spec.spl` |
| `test/nvfs/nvfs_remount_persistence_spec.spl` | `test/02_integration/storage/nvfs/nvfs_remount_persistence_spec.spl` |
| `test/nvfs/nvfs_superblock_disk_spec.spl` | `test/02_integration/storage/nvfs/nvfs_superblock_disk_spec.spl` |

Verification: `SIMPLE_LIB=src bin/simple test --force-rebuild test/02_integration/storage/nvfs`
passed 21/21 across five files.

### 2026-05-28 Batch 28

Moved the top-level tools root into canonical unit, system, and fixture
buckets. Pure command/model specs moved to unit coverage, platform/deploy
behavior moved to system coverage, CI helper scripts moved to fixtures, and
saved `summary.txt` evidence moved under `test/fixtures/tools/evidence`.

| Old path | New mirrored path |
|---|---|
| `test/tools/*_spec.spl` | `test/01_unit/tools/*_spec.spl` |
| `test/tools/shell/*_spec.spl` | `test/01_unit/tools/shell/*_spec.spl` |
| `test/tools/desktop/*_spec.spl` | `test/01_unit/tools/desktop/*_spec.spl` |
| `test/tools/simple_os_primary_spec.spl` | `test/01_unit/tools/simple_os_primary_spec.spl` |
| `test/tools/deploy/smoke_spec.spl` | `test/03_system/tools/deploy/smoke_spec.spl` |
| `test/tools/manual/platform_spec_verification_spec.spl` | `test/03_system/tools/manual/platform_spec_verification_spec.spl` |
| `test/tools/ci/*.spl` | `test/fixtures/tools/ci/*.spl` |
| `test/tools/**/summary.txt` | `test/fixtures/tools/evidence/**` |

Verification: representative moved specs passed:
`test/01_unit/tools/echo_spec.spl` 5/5,
`test/01_unit/tools/shell/seq_spec.spl` 3/3,
`test/01_unit/tools/desktop/primary_cli_model_spec.spl` 3/3,
`test/01_unit/tools/simple_os_primary_spec.spl` 4/4,
`test/03_system/tools/manual/platform_spec_verification_spec.spl` 4/4, and
`test/03_system/tools/deploy/smoke_spec.spl` 4/4. `test/01_unit/tools/cat_spec.spl`
exited 0 with a 4/4 summary but also printed a contradictory per-file
`FAILED` line, matching the existing runner-output anomaly noted in earlier
tooling checks.

### 2026-05-28 Batch 29

Moved the top-level DBFS storage root into canonical storage integration and
fixture buckets. Executable DBFS, hosted filesystem, parser, WAL, recovery, and
benchmark smoke specs moved under `test/02_integration/storage/dbfs`. Shared
benchmark harnesses, passthrough helpers, and hosted fixtures moved under
`test/fixtures/storage/dbfs`.

| Old path | New mirrored path |
|---|---|
| `test/dbfs/*_spec.spl` | `test/02_integration/storage/dbfs/*_spec.spl` |
| `test/dbfs/bench_*.spl` | `test/fixtures/storage/dbfs/bench/*.spl` |
| `test/dbfs/*harness.spl` | `test/fixtures/storage/dbfs/harness/*.spl` |
| `test/dbfs/*shared.spl` | `test/fixtures/storage/dbfs/*.spl` |

Verification: representative moved specs passed:
`test/02_integration/storage/dbfs/dbfs_recovery_spec.spl` 9/9,
`test/02_integration/storage/dbfs/dbfs_no_regression_spec.spl` 5/5,
`test/02_integration/storage/dbfs/dbfs_driver_spec.spl` 8/8,
`test/02_integration/storage/dbfs/fts_engine_spec.spl` 28/28, and
`test/02_integration/storage/dbfs/dbfs_engine_wal_spec.spl` 8/8. Existing DB/SQL
coverage still fails after the move:
`test/02_integration/storage/dbfs/pure_db_spec.spl` reported 41 passed and 18
failed, and `test/02_integration/storage/dbfs/pure_db_sql_extended_spec.spl`
reported 8 passed and 2 failed. `bench_comparison_spec.spl` exited 0 with an
all-pass summary but printed the same contradictory runner failure anomaly seen
in tooling checks.

### 2026-05-28 Batch 30

Moved browser and rendering compatibility roots into canonical unit, feature,
and system buckets. Direct browser-engine module specs moved to
`test/01_unit/browser_engine`, WPT-shaped web-platform coverage moved to
`test/03_system/feature/web_platform`, and the reftest parity harness moved as a coupled
system package under `test/03_system/reftest`.

| Old path | New mirrored path |
|---|---|
| `test/browser_engine/*` | `test/01_unit/browser_engine/*` |
| `test/08_web_platform/*` | `test/03_system/feature/web_platform/*` |
| `test/reftest/parity/*` | `test/03_system/reftest/parity/*` |

Verification: discovery passed for the moved roots:
`bin/simple test test/01_unit/browser_engine --list` listed 252 tests,
`bin/simple test test/03_system/feature/web_platform --list` listed 398 tests, and
`bin/simple test test/03_system/reftest --list` listed 35 tests. Focused
`test/03_system/reftest/parity/pixel_diff_core_spec.spl` passed 15/15.
Existing failures remain visible after the move: browser-engine net and
web-platform scorecard checks crash on unresolved `rt_native_eq`, and reftest
parity specs still fail behavior assertions despite their moved imports
resolving.

### 2026-05-28 Batch 31

Moved QEMU and FPGA hardware-gated roots into canonical system buckets. QEMU
specs, summaries, and the shared OS harness moved under `test/03_system/qemu` so
runner classification and timeout logic still see a `/qemu/` path component.
RISC-V FPGA preflight, manifest, inventory, JTAG, and payload checks moved
under `test/03_system/hardware/riscv64_fpga`.

| Old path | New mirrored path |
|---|---|
| `test/qemu/**` | `test/03_system/qemu/**` |
| `test/riscv64_fpga/*_spec.spl` | `test/03_system/hardware/riscv64_fpga/*_spec.spl` |

Verification: focused moved and affected checks passed:
`test/01_unit/lib/test_runner/test_classification_system_routing_spec.spl` 9/9,
`test/03_system/qemu/qmp_screendump_spec.spl` 5/5,
`test/01_unit/qemu/qemu_harness_acquire_or_spawn_spec.spl` 8/8, and
`test/03_system/hardware/riscv64_fpga` 91/91. Exact old-path reference scans for
`test/qemu`, `test/riscv64_fpga`, and `test.qemu.os` passed outside this
migration map and its parent plan.

### 2026-05-28 Batch 32

Moved the top-level app test root into canonical unit and integration buckets.
Module-level ITF, SVim, render type, and test API specs moved under
`test/01_unit/app`; app workflow, service, process, UI-web, diagnostics, release,
portal, MCP, optimizer, document navigation, and summary evidence moved under
`test/02_integration/app`.

| Old path | New mirrored path |
|---|---|
| `test/app/itf/*_spec.spl` | `test/01_unit/app/itf/*_spec.spl` |
| `test/app/svim/*_spec.spl` | `test/01_unit/app/svim/*_spec.spl` |
| `test/app/ui.render/types*` | `test/01_unit/app/ui.render/types*` |
| `test/app/ui.test_api/*` | `test/01_unit/app/ui.test_api/*` |
| `test/app/**` | `test/02_integration/app/**` |

Verification: discovery passed for `test/01_unit/app/itf` with 219 listed tests,
`test/01_unit/app/svim` with 72 listed tests, `test/02_integration/app/ui.web` with
158 listed tests, and `test/02_integration/app/diagnostics` with 13 listed tests.
Focused checks passed for `test/01_unit/app/itf/itf_flags_spec.spl` 10/10 and
`test/02_integration/app/ui.web/random_hex_test.spl` 8/8. Existing behavioral
failures remain after the move:
`test/01_unit/app/svim/core_spec.spl` reported 19 passed and 6 failed, and
`test/01_unit/app/ui.test_api/handler_test.spl` reported 61 passed and 9 failed.

### 2026-05-28 Batch 33

Moved the top-level OS test root into canonical unit, integration, system, and
fixture buckets. Direct compositor, driver, kernel, desktop manifest resolver,
and non-boot multiarch checks moved under `test/01_unit/os`. Port/toolchain/static
orchestration checks moved under `test/02_integration/os/port`. QEMU, E2E, boot,
and runtime-gated checks moved under `test/03_system/os`. Port audit C fixtures
moved under `test/fixtures/os/port`. Kernel logging specs use
`test/01_unit/os/kernel/logging` because `log/` is ignored by `.gitignore`.

| Old path | New mirrored path |
|---|---|
| `test/os/compositor/*` | `test/01_unit/os/compositor/*` |
| `test/os/desktop/app_manifest_resolver*` | `test/01_unit/os/desktop/app_manifest_resolver*` |
| `test/os/drivers/*` | `test/01_unit/os/drivers/*` |
| `test/os/kernel/**` | `test/01_unit/os/kernel/**` |
| `test/os/multiarch/*` | `test/01_unit/os/multiarch/*` or `test/03_system/os/multiarch/*` by boot/runtime coupling |
| `test/os/port/*` | `test/02_integration/os/port/*`, `test/03_system/os/port/*`, or `test/fixtures/os/port/*` by role |

Verification: focused checks passed for
`test/03_system/os/desktop/taskbar_shell_qemu_test.spl` 12/12 and
`test/02_integration/os/port/disk_image_bake_spec.spl` 8/8. Discovery passed for
`test/01_unit/os/kernel` with 1136 listed tests, `test/02_integration/os/port` with
73 listed tests, and `test/03_system/os/port` with 36 listed tests. Existing
failures remain after the move in stack builder, bootstrap cross status, disk
boot, syscall shim, Simple-from-FS, and HAL trait-surface specs; compositor
web-surface blit hung and was killed. The moved
`test/01_unit/os/kernel/logging/marker_wire_format_spec.spl` exists but runner
discovery reported 0 files, requiring follow-up.

### 2026-05-28 Batch 34

Moved the remaining top-level lib root into canonical unit and fixture buckets.
Most library-domain specs moved under matching `test/01_unit/lib/...` subtrees.
The transitive import executable spec and summary moved under
`test/01_unit/lib/transitive`, while helper modules moved under
`test/fixtures/lib/transitive` and imports were updated to the fixture module
path.

| Old path | New mirrored path |
|---|---|
| `test/lib/{blink,cc,common,content,ecs,editor,gui,hal,mcp,nogc_async_mut,nogc_async_mut_noalloc,nogc_sync_mut,skia,spec,text,viz}/**` | `test/01_unit/lib/...` |
| `test/lib/transitive/transitive_import_spec.spl` | `test/01_unit/lib/transitive/transitive_import_spec.spl` |
| `test/lib/transitive/summary.txt` | `test/01_unit/lib/transitive/summary.txt` |
| `test/lib/transitive/module_b.spl` | `test/fixtures/lib/transitive/module_b.spl` |
| `test/lib/transitive/module_c.spl` | `test/fixtures/lib/transitive/module_c.spl` |

Verification: `test/01_unit/lib/blink --list` passed with 182 listed tests,
`test/01_unit/lib/transitive --list` passed with 1 listed test, and
`test/01_unit/lib/transitive/transitive_import_spec.spl` passed 1/1. Existing
failures remain in moved common Wine substrate, MCP lazy loading, Skia matrix,
HAL types, text length, bytes pointer, and ECS specs. The moved
`.spipe_matchers_*` files under `test/01_unit/lib/nogc_async_mut/...` are ignored
by `.gitignore`, so staging this slice will require force-adding those
previously tracked matcher files.

## Root-Level Files

| File | Likely owner | Canonical target | Safe next move |
|---|---|---|---|
| `doc/06_spec/INDEX.md` | Global doc index | keep root | Keep; update after migration tooling is stable. |
| `doc/06_spec/README.md` | Global layout guide | keep root | Keep; already documents canonical layout. |
| `doc/06_spec/feature/language/async_default_spec.md` | `test/03_system/feature/language/async_default_spec.spl` | `doc/06_spec/feature/language/async_default_spec.md` or `doc/06_spec/feature/compiler/async_default_spec.md` | Confirm whether `test/03_system/feature/language` migrates to `test/03_system/feature/compiler`; then regenerate. |
| `doc/06_spec/bootstrap_test_gate.sdn` | `doc/02_requirements/feature/remote_jit_exec_hardening.sdn` | data owner TBD | Leave in place until SDN consumer is found. |
| `doc/06_spec/feature/language/capability_effects_spec.md` | `test/03_system/feature/language/capability_effects_spec.spl` | `doc/06_spec/feature/language/capability_effects_spec.md` | Confirm `test/03_system/feature/language` destination; regenerate. |
| `doc/06_spec/ch32v307_composite_runner_path_spec.md` | `test/02_integration/remote_jit/ch32v307_composite_runner_path_spec.spl` | `doc/06_spec/integration/remote_jit/ch32v307_composite_runner_path_spec.md` | Done in Batch 1. |
| `doc/06_spec/feature/language/concurrency_spec.md` | `test/03_system/feature/language/concurrency_spec.spl` | `doc/06_spec/feature/language/concurrency_spec.md` | Confirm `test/03_system/feature/language` destination; regenerate. |
| `doc/06_spec/feature/app/web_dashboard/dashboard_render_spec.md` | `test/03_system/feature/app/web_dashboard/dashboard_render_spec.spl` | `doc/06_spec/feature/app/web_dashboard/dashboard_render_spec.md` | Done in Batch 6. |
| `doc/06_spec/feature/language/data_structures_spec.md` | `test/03_system/feature/language/data_structures_spec.spl` | `doc/06_spec/feature/language/data_structures_spec.md` | Confirm `test/03_system/feature/language` destination; regenerate. |
| `doc/06_spec/feature.md` | Feature category inventory | generated/catalog TBD | Do not move until inventory generator ownership is known. |
| `doc/06_spec/feature_db.sdn` | `test/01_unit/app/tooling/feature_db_spec.spl` plus stats tooling | data owner TBD | Leave in place; document consumer before moving. |
| `doc/06_spec/feature/language/functions_spec.md` | `test/03_system/feature/language/functions_spec.spl` | `doc/06_spec/feature/language/functions_spec.md` | Confirm `test/03_system/feature/language` destination; regenerate. |
| `doc/06_spec/feature/usage/loss_nograd_blocks_spec.md` | `test/03_system/feature/usage/loss_nograd_blocks_spec.spl` | `doc/06_spec/feature/usage/loss_nograd_blocks_spec.md` | Done in Batch 20; root duplicate removed. |
| `doc/06_spec/feature/language/macro_spec.md` | `test/03_system/feature/language/macro_spec.spl` | `doc/06_spec/feature/language/macro_spec.md` | Confirm `test/03_system/feature/language` destination; regenerate. |
| `doc/06_spec/feature/usage/math_blocks_spec.md` | `test/03_system/feature/usage/math_blocks_spec.spl` | `doc/06_spec/feature/usage/math_blocks_spec.md` | Done in Batch 20; root duplicate removed and richer mirrored doc kept. |
| `doc/06_spec/feature/usage/math_render_spec.md` | `test/03_system/feature/usage/math_render_spec.spl` | `doc/06_spec/feature/usage/math_render_spec.md` | Done in Batch 20; root duplicate removed. |
| `doc/06_spec/feature/language/memory_spec.md` | `test/03_system/feature/language/memory_spec.spl` | `doc/06_spec/feature/language/memory_spec.md` | Confirm `test/03_system/feature/language` destination; regenerate. |
| `doc/06_spec/metaprogramming.md` | `test/03_system/feature/usage/metaprogramming_spec.spl`; also `test/03_system/feature/language/macro_spec.spl` hints | `doc/06_spec/feature/usage/metaprogramming_spec.md` | Done in Batch 3; macro overlap remains a later comparison task. |
| `doc/06_spec/feature/language/modules_spec.md` | `test/03_system/feature/language/modules_spec.spl` | `doc/06_spec/feature/language/modules_spec.md` | Confirm `test/03_system/feature/language` destination; regenerate. |
| `doc/06_spec/pending_feature.md` | Feature inventory/stats tooling | generated/catalog TBD | Leave until generator and destination catalog are defined. |
| `doc/06_spec/qemu_rv32_raw_injected_regression_spec.md` | `test/02_integration/remote_jit/qemu_rv32_raw_injected_regression_spec.spl` | `doc/06_spec/integration/remote_jit/qemu_rv32_raw_injected_regression_spec.md` | Done in Batch 1. |
| `doc/06_spec/feature/app/remote_baremetal/remote_baremetal_library_spec.md` | `test/03_system/feature/app/remote_baremetal/remote_baremetal_library_spec.spl` | `doc/06_spec/feature/app/remote_baremetal/remote_baremetal_library_spec.md` | Done in Batch 4. |
| `doc/06_spec/feature/app/remote_baremetal/remote_baremetal_runtime_spec.md` | `test/03_system/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl` | `doc/06_spec/feature/app/remote_baremetal/remote_baremetal_runtime_spec.md` | Done in Batch 4. |
| `doc/06_spec/sandboxing.md` | `test/03_system/feature/usage/sandboxing_spec.spl` | `doc/06_spec/feature/usage/sandboxing_spec.md` | Done in Batch 3. |
| `doc/06_spec/shell_api.md` | `test/03_system/feature/app/shell_api_spec.spl` | `doc/06_spec/feature/app/shell_api_spec.md` | Done in Batch 3. |
| `doc/06_spec/feature/language/suspension_operator_spec.md` | `test/03_system/feature/language/suspension_operator_spec.spl` | duplicate of `_spec` markdown | Compare with `suspension_operator_spec.md`, then delete or redirect duplicate. |
| `doc/06_spec/suspension_operator_spec.md` | `test/03_system/feature/language/suspension_operator_spec.spl` | `doc/06_spec/feature/language/suspension_operator_spec.md` | Confirm `test/03_system/feature/language` destination; regenerate. |
| `doc/06_spec/feature/usage/syntax_spec.md` | `test/03_system/feature/usage/syntax_spec.spl`; older non-identical compiler copy also exists under `app/compiler/feature/usage` | `doc/06_spec/feature/usage/syntax_spec.md` | Done in Batch 5; compare older compiler copy later. |
| `doc/06_spec/feature/ml/tensor_dimensions_spec.md` | `test/03_system/feature/ml/tensor_dimensions_spec.spl` | `doc/06_spec/feature/ml/tensor_dimensions_spec.md` | Done in Batch 8. |
| `doc/06_spec/unit/lib/std/tmux/tmux_api_spec.md` | `test/01_unit/lib/std/tmux/tmux_api_spec.spl` | `doc/06_spec/unit/lib/std/tmux/tmux_api_spec.md` | Done in Batch 7. |
| `doc/06_spec/feature/app/web_dashboard/tmux_rest_api_spec.md` | `test/03_system/feature/app/web_dashboard/tmux_rest_api_spec.spl` | `doc/06_spec/feature/app/web_dashboard/tmux_rest_api_spec.md` | Done in Batch 6. |
| `doc/06_spec/feature/language/traits_spec.md` | `test/03_system/feature/language/traits_spec.spl` | `doc/06_spec/feature/language/traits_spec.md` | Confirm `test/03_system/feature/language` destination; regenerate. |
| `doc/06_spec/feature/language/type_inference_spec.md` | `test/03_system/feature/language/type_inference_spec.spl` | `doc/06_spec/feature/language/type_inference_spec.md` | Confirm `test/03_system/feature/language` destination; regenerate. |
| `doc/06_spec/types.md` | `test/03_system/feature/usage/types_spec.spl` | `doc/06_spec/feature/usage/types_spec.md` | Done in Batch 3; broader type-system duplicate docs remain for later comparison. |

## Legacy And Runtime Files

| File | Likely owner | Canonical target | Safe next move |
|---|---|---|---|
| `doc/06_spec/legacy/INDEX.md` | Legacy navigation | deleted | Done in Batch 21. |
| `doc/06_spec/legacy/command_dispatch_spec.md` | `test/01_unit/app/tooling/command_dispatch_spec.spl` | `doc/06_spec/unit/app/tooling/command_dispatch_spec.md` | Done in Batch 1. |
| `doc/06_spec/legacy/test-spec.html` | Old docgen fixture/output | deleted | Done in Batch 21. |
| `doc/06_spec/legacy/test-spec.md` | Old docgen fixture/output | deleted | Done in Batch 21. |
| `doc/06_spec/legacy/test_runner_simple_spec.md` | `test/01_unit/app/tooling/test_runner_simple_spec.spl` | `doc/06_spec/unit/app/tooling/test_runner_simple_spec.md` | Done in Batch 1. |
| `doc/06_spec/feature/app/remote_jit/trace32_stm32h7_jit_e2e_spec.md` | `test/03_system/feature/app/remote_jit/trace32_stm32h7_jit_e2e_spec.spl` | `doc/06_spec/feature/app/remote_jit/trace32_stm32h7_jit_e2e_spec.md` | Done in Batch 21. |
| `doc/06_spec/runtime/rt_gui_glass_contract.md` | Runtime GUI manual contract; no direct source spec found | `doc/06_spec/runtime/gui/rt_gui_glass_contract.md` or design doc | Manual review; add source spec if this remains a release contract. |

## Safe Next Moves

1. Use the repaired pure-Simple `spipe-docgen` path for the next generated-doc
   batches. Direct interpreter invocation now writes mirrored feature docs.
2. Regenerate remaining high-confidence one-to-one files that still have stale
   or non-identical legacy copies: placeholder lambda, decorators, and
   type-checker specs are the current priority.
3. Leave SDN/catalog files in place until their producers and consumers are
   explicitly traced.
4. After a small migration batch, run traceability checks and doc navigation
   tests before moving the next batch.
5. Broader test-layout candidates identified by sidecar review: top-level
   temporary/experimental roots (`test/tmp_verify_quality`, `test/scratch`,
   `test/spike`), duplicate category aliases (`test/features`, `test/sys`,
   `test/smoke`), and domain-first roots (`test/app`, `test/compiler`,
   `test/browser_engine`, `test/code_quality`, `test/dbfs`, `test/hal`,
   `test/js`, `test/nvfs`, `test/os`, `test/qemu`, `test/reftest`,
   `test/riscv64_fpga`, `test/rtl`, `test/runtime`, `test/sffi`,
   `test/tools`, `test/web_platform`). Most listed roots are now resolved in
   the completed batches above. `test/shared` is now resolved as a canonical
   cross-platform runner tier, not a fixture cleanup; its known imported
   contract spec has moved to the unit contract helper bucket.

## Tooling Repair

### 2026-05-28 Pure-Simple `spipe-docgen`

The pure-Simple `spipe-docgen` implementation was structurally repaired by
moving modules from `src/app/spipe_docgen/spipe_docgen/` to
`src/app/spipe_docgen/`. This matches the existing command table path
`src/app/spipe_docgen/main.spl` and imports such as
`app.spipe_docgen.common`.

Additional fixes in the same tooling slice:

- `common.spl` imports filesystem/process primitives directly instead of
  importing the compiler-driver-heavy `app.io.mod` surface.
- `main.spl` normalizes direct script invocation arguments and computes the
  fallback output filename after the file stem exists.
- `parser.spl` avoids a shadowed `block_lines` binding that made a mutable
  array look immutable under the current interpreter.
- `generator.spl` creates nested output directories before writing mirrored
  docs.

Verification:

- `SIMPLE_LIB=src SIMPLE_EXECUTION_MODE=interpret bin/simple --interpret src/app/spipe_docgen/main.spl test/03_system/feature/language/placeholder_lambda_spec.spl --output /tmp/spipe-docgen-probe`
  completed successfully and generated
  `/tmp/spipe-docgen-probe/feature/language/placeholder_lambda_spec.md`.
- `SIMPLE_LIB=src bin/simple test --force-rebuild test/01_unit/app/tooling/command_dispatch_spec.spl`
  passed with 105 examples.
- `SIMPLE_LIB=src bin/simple test --force-rebuild test/01_unit/app/tooling/spipe_docgen_scenario_body_spec.spl`
  reported 8 passed examples and process exit 0, but also printed an internal
  `FAILED`/`Process exited with code 1` line.
