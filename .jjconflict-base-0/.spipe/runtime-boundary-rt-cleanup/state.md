# Feature: runtime-boundary-rt-cleanup

## Raw Request

remove rt use except is infra provide, improve simple gen code make it better perf and make simple to handle hw direct if can't. fix simple lang perf bug, baremetal feature rack. add this to refactor skill and verification skill. to remove if possible.

## Task Type

code-quality

## Refined Goal

Make direct `rt_*` use a verified infrastructure-only boundary and create a scoped path for removing ordinary Simple runtime bypasses in favor of generated/native Simple or direct-hardware backends.

## Acceptance Criteria

- AC-1: `.codex/skills/refactor/SKILL.md` tells refactor agents to remove direct `rt_*` use unless it is an infrastructure/provider boundary or has a linked compiler/runtime, performance, or baremetal/direct-hardware blocker.
- AC-2: `.codex/skills/verify/SKILL.md` treats new non-provider direct `rt_*` use as a verification failure unless a concrete blocker is linked.
- AC-3: A tracking artifact records the runtime-boundary cleanup policy, existing broad `rt_*` footprint, and why wholesale removal is not safe without classification.
- AC-4: The current repo has a focused audit identifying candidate `rt_*` call-site groups as provider/evidence/ordinary-code before any deletion.
- AC-5: At least one safe ordinary-code `rt_*` use is removed or rewritten through an existing stdlib/capability wrapper, if such a candidate exists in the focused audit.
- AC-6: The SPipe command routing check passes and `doc/06_spec` contains no executable `*_spec.spl` files.

## Scope Exclusions

- Do not delete SFFI, runtime, OS/QEMU, GPU, generated SPipe wrapper, or test evidence `rt_*` use without a separate owner-specific lane.
- Do not implement a new hardware backend or compiler optimization without a concrete failing benchmark/spec naming the exact bug.

## Phase

dev-done

## Log

- dev: Created state file with 6 acceptance criteria (type: code-quality).
- impl: Added refactor/verify runtime-boundary gates, created tracking artifact,
  classified focused `rt_*` groups, and removed raw `rt_file_read_text` from
  `test/02_integration/spec/runner_spec.spl`.
- impl: Removed additional ordinary-test raw `rt_*` process/file externs from
  `test/ci/shell_exec.spl`,
  `test/03_system/check/renderdoc_simple_gate_spec.spl`, and
  `test/03_system/check/directx_native_readback_spec.spl`.
- impl: Removed more ordinary-test raw `rt_*` externs from
  `test/01_unit/tooling/renderdoc_capture_infra_spec.spl`,
  `test/01_unit/tools/ls_spec.spl`, and
  `test/01_unit/t32_mcp/lifecycle_tools_spec.spl`.
- impl: Removed ordinary process/file raw `rt_*` externs from
  `test/02_integration/app/gen_lean_log_modes_spec.spl`,
  `test/02_integration/app/linkers_log_modes_spec.spl`, and
  `test/03_system/check/html_css_renderdoc_goal_status_spec.spl`; rejected
  launcher and diff-log conversions after focused checks showed they were not
  safe inline cleanups.
- impl: Removed more ordinary source-read/native-IO raw `rt_*` externs from
  `test/02_integration/spec/formatter_spec.spl`,
  `test/02_integration/compiler/static_method_desugar_spec.spl`, and
  `test/02_integration/io/native_ops_*_spec.spl`; added native IO manual
  headers to keep docgen complete.
- impl: Removed ordinary source/local-file raw `rt_*` externs from
  `test/01_unit/std/context_spec.spl`, `test/01_unit/std/condition_spec.spl`,
  `test/02_integration/examples/platform_library_example_spec.spl`,
  `test/02_integration/app/web_stack_sample_spec.spl`, and
  `test/02_integration/app/web_stack_sample_browser_spec.spl`; rejected
  `test/02_integration/ffi_gen/math_migration_test.spl` after focused checks
  failed outside the wrapper change.
- impl: Removed raw diagnostics source-read externs from
  `test/01_unit/compiler_shared/diagnostics/{span,severity,label,diagnostic}_spec.spl`
  and fixed the label spec's interpolated expected string.
- impl: Removed raw compiler-core source-read externs from
  `test/01_unit/compiler_core/{types,type_subst,traits,traits_module}_spec.spl`;
  verified the four focused specs and regenerated complete docs with 0 stubs.
- impl: Removed production editor host-IO raw externs from
  `src/lib/editor/core/{workspace,wal,recovery,recent}.spl` and
  `src/lib/editor/extensions/manifest.spl`; focused checks passed and raw scan
  found no remaining `rt_*` calls in that batch.
- impl: Removed more editor persistence raw externs from
  `src/lib/editor/00.common/{config,keybindings}.spl`,
  `src/lib/editor/core/document.spl`, and `src/lib/editor/buffer/buffer.spl`;
  focused checks passed and raw scan found no remaining `rt_*` calls in that
  batch.
- impl: Added the missing `std.io_runtime.dir_walk` provider wrapper/export,
  removed direct editor file/directory `rt_*` use from unified navigation,
  file-watcher/search/md-search, and extension host code, then updated and
  verified the extension discovery/gui specs with complete docgen output.
- impl: Removed raw source/process runtime calls from
  `test/02_integration/simpleos_driver_log_smoke_spec.spl` and
  `test/03_system/lib/pure_simple_ssh_https_servers/pure_simple_server_release_smoke_spec.spl`;
  fixed the SimpleOS driver spec's stale null-block driver path and verified
  both specs with complete docgen output.
- impl: Removed duplicated raw runtime wrappers from
  `test/05_perf/cli_dispatch_perf_spec.spl`; raw scan is clean and docgen is
  complete, but the focused perf spec still reports 8 passed / 1 failed, so the
  remaining perf/test-runner issue is tracked in
  `doc/08_tracking/bug/cli_dispatch_perf_spec_failure_2026-06-21.md`.
- impl: Removed raw timer/exit helpers from
  `test/05_perf/ctype/{global_static_array_smoke,bench_ctype_static_lut}.spl`
  and fixed the missing static LUT exports in `ctype_lut_tables.spl`; focused
  checks passed and `global_static_array_smoke.spl` prints `[ctype-static-array]
  ok`.
- impl: Removed direct file/env runtime calls from `src/lib/sdn/__init__.spl`
  and `src/lib/scv/wasm_executor.spl`; focused raw scans were clean and both
  files passed `bin/simple check`.
- impl: Removed direct package-manifest file runtime calls from
  `src/app/pkg/manifest.spl`; focused raw scan was clean and `bin/simple check`
  passed after deleting stale unused `std.sdn` imports.
- impl: Removed raw process/file runtime calls from the HTML/CSS SSpec and
  rendering-manifest traceability specs; focused raw scans were clean, both
  specs passed, and docgen completed with 0 stubs.
- impl: Removed raw compiler source-read calls from
  `test/01_unit/compiler_core/{traits_extended,traits_compiles,tokens,new_tokens}_spec.spl`;
  focused raw scan was clean, all four specs passed, and docgen completed with
  0 stubs.
- impl: Removed raw compiler source-read calls from
  `test/01_unit/compiler_core/{pragma_msg,lang_basics,receive,tmp_test,keyof_token,must_use}_spec.spl`,
  `test/01_unit/compiler_core/entity/{entity_structure,entity_span}_spec.spl`,
  and `test/01_unit/compiler_core/interpreter/{value,ops,jit}_spec.spl`;
  focused raw scan was clean, all 11 specs passed, and docgen completed with
  0 stubs.
- impl: Rejected `test/03_system/compiler/{import_c_match,struct_reorder}_spec.spl`
  as inline runtime-boundary cleanups because stale source expectations already
  make the focused specs fail; reverted the attempted wrapper swap.
- impl: Removed raw source-read runtime calls from
  `test/03_system/gui/editor_markdown_spec.spl`; baseline and post-edit focused
  specs passed, raw scan was clean, and docgen completed with 0 stubs.
- impl: Rejected `test/03_system/gui/editor_md_wiki_index_spec.spl` for inline
  cleanup because the focused spec is already failing before any edit.
- impl: Removed raw file-existence runtime calls from
  `test/03_system/tools/deploy/smoke_spec.spl`; baseline and post-edit focused
  specs passed, raw scan was clean, and docgen completed with 0 stubs.
- impl: Rejected `test/02_integration/storage/dbfs/mem_block_device_spec.spl`
  and `test/03_system/compiler/compiler_interpret_pipeline_spec.spl` for inline
  cleanup because focused baseline runs are already failing before any edit.
- impl: Removed raw source-read runtime calls from
  `test/02_integration/os/port/runtime_bundle_policy_spec.spl`; baseline and
  post-edit focused specs passed, raw scan was clean, and docgen completed with
  0 stubs.
- impl: Removed the raw environment runtime call from
  `test/02_integration/os/port/native_convergence_spec.spl`; baseline and
  post-edit focused specs passed, raw scan was clean, and docgen completed with
  0 stubs.
- impl: Removed raw source-read/file-existence runtime calls from
  `test/02_integration/os/port/bootstrap_seed_fallback_policy_spec.spl`;
  baseline and post-edit focused specs passed, raw scan was clean, and docgen
  completed with 0 stubs.
- impl: Removed raw source-read runtime calls from
  `test/02_integration/os/port/bootstrap_cross_status_spec.spl`; baseline and
  post-edit focused specs passed, raw scan was clean, and docgen completed with
  0 stubs.
- impl: Removed raw source-read runtime calls from
  `test/02_integration/os/port/disk_image_bake_spec.spl`; baseline and
  post-edit focused specs passed, raw scan was clean, and docgen completed with
  0 stubs.
- impl: Left sampled REPL system specs unchanged because focused baseline runs
  failed before any runtime-boundary edit.
- impl: Removed the raw subprocess runtime call from
  `test/03_system/tools/simple_lsp_protocol_live_spec.spl`; baseline and
  post-edit focused specs passed, raw scan was clean, and docgen completed with
  0 stubs.
- impl: Removed the raw subprocess runtime call from
  `test/03_system/tools/nvim_plugin_live_spec.spl`; baseline and post-edit
  focused specs passed, raw scan was clean, and docgen completed with 0 stubs.
- impl: Left sampled LSP and lint system specs unchanged because focused
  baseline runs timed out before any runtime-boundary edit.
- impl: Removed unused file/env runtime externs and raw subprocess runtime calls
  from `test/03_system/tools/bootstrap_mcp_spec.spl`; baseline and post-edit
  focused specs passed, raw scan was clean, and docgen completed with 0 stubs.
- impl: Removed raw file, directory, pid, and timer runtime calls from
  `test/03_system/tools/test_daemon/test_daemon_flow_system_spec.spl`;
  baseline and post-edit focused specs passed, raw scan was clean, and docgen
  completed with 0 stubs.
- impl: Removed raw file, directory, pid, and timer runtime calls from
  `test/03_system/tools/test_daemon/test_daemon_concurrent_spec.spl`;
  baseline and post-edit focused specs passed, raw scan was clean, and docgen
  completed with 0 stubs.
