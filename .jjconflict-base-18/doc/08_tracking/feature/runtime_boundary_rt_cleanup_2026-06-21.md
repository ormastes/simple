# Runtime Boundary `rt_*` Cleanup

Status: current

## Goal

Remove direct `rt_*` extern use from ordinary Simple code. Keep `rt_*` only at
infrastructure/provider boundaries that expose capabilities to higher layers.

## Policy

- Prefer generated/native Simple, stdlib wrappers, capability records, traits,
  or direct hardware backends over runtime bypasses.
- If Simple cannot express the required hardware path yet, record the specific
  compiler/runtime performance or baremetal/direct-hardware blocker before
  keeping the bridge.
- Baremetal hot paths should stay in generated/native Simple where possible;
  runtime glue is limited to board/host services such as boot, MMIO, interrupts,
  clocks, DMA, process/filesystem access, and probes.

## Initial Audit

`rg '^\\s*extern fn rt_|\\brt_[A-Za-z0-9_]+' src test -g '*.spl'` currently
finds broad use in SFFI, runtime, OS/QEMU, GPU, generated SPipe wrappers, and
tests. Most of that is likely provider or evidence code. Removal needs a scoped
lane that classifies call sites before deleting anything.

## Focused Classification

| Group | Example paths | Classification | Action |
| --- | --- | --- | --- |
| Runtime/core providers | `src/runtime/simple_core/*`, `src/lib/nogc_sync_mut/sffi/*` | provider boundary | Keep until a pure/generated Simple replacement exists. |
| OS, QEMU, baremetal, MMIO/DMA/network | `src/os/**`, `test/03_system/os/**` | provider/evidence boundary | Keep; track direct-hardware gaps separately. |
| GPU, graphics, torch, BLAS SFFI | `src/lib/**/gpu/**`, `src/lib/**/torch/**`, `src/lib/**/linalg/**` | provider boundary | Keep unless replaced by generated backend code. |
| Generated SPipe wrappers | `.spipe_wrapped_entry_*`, `.spipe_matchers_*` | generated evidence | Do not hand-edit; fix source specs instead. |
| Ordinary tests/specs | `test/02_integration/spec/runner_spec.spl`, `test/ci/shell_exec.spl`, selected `test/03_system/check/*_spec.spl` | removable wrapper bypass | Rewritten to `std.io_runtime.file_read` / `process_run`. |
| Editor library host IO | `src/lib/editor/core/*`, `src/lib/editor/extensions/*` | removable wrapper bypass | Route through `std.io_runtime`; keep raw `rt_*` only in provider modules. |

## Workflow Hooks

- Refactor skill: `.codex/skills/refactor/SKILL.md` runtime boundary audit.
- Verify skill: `.codex/skills/verify/SKILL.md` runtime boundary NFR gate.

## Removed In This Lane

- `test/02_integration/spec/runner_spec.spl`: removed direct
  `extern fn rt_file_read_text` and routed file reads through
  `std.io_runtime.file_read`.
- `test/ci/shell_exec.spl`: routed shell execution through
  `std.io_runtime.process_run`.
- `test/03_system/check/renderdoc_simple_gate_spec.spl`: routed process and
  file evidence reads through `std.io_runtime`.
- `test/03_system/check/directx_native_readback_spec.spl`: routed process and
  file evidence reads through `std.io_runtime`.
- `test/01_unit/tooling/renderdoc_capture_infra_spec.spl`: routed process and
  file reads through `std.io_runtime`.
- `test/01_unit/tools/ls_spec.spl`: routed file-existence checks through
  `std.io_runtime.file_exists`.
- `test/01_unit/t32_mcp/lifecycle_tools_spec.spl`: routed environment, file,
  and process checks through `std.io_runtime`; removed host-specific assumptions
  about `/opt/t32` and `xvfb-run`.
- `test/02_integration/app/gen_lean_log_modes_spec.spl`: routed process
  execution through `std.io_runtime.process_run`.
- `test/02_integration/app/linkers_log_modes_spec.spl`: routed process
  execution through `std.io_runtime.process_run`.
- `test/03_system/check/html_css_renderdoc_goal_status_spec.spl`: routed process
  and file evidence reads through `std.io_runtime`.
- `test/02_integration/spec/formatter_spec.spl`: routed source reads through
  `std.io_runtime.file_read`.
- `test/02_integration/compiler/static_method_desugar_spec.spl`: routed source
  reads through `std.io_runtime.file_read`.
- `test/02_integration/io/native_ops_*_spec.spl`: routed temp-dir environment
  lookup and shell process calls through `std.io_runtime`; added short manual
  headers so generated docs are complete rather than auto-stubbed.
- `test/01_unit/std/context_spec.spl` and
  `test/01_unit/std/condition_spec.spl`: routed source reads through
  `std.io_runtime.file_read`.
- `test/02_integration/examples/platform_library_example_spec.spl`: routed local
  text file read/write/delete helpers through `std.io_runtime`.
- `test/02_integration/app/web_stack_sample_spec.spl` and
  `test/02_integration/app/web_stack_sample_browser_spec.spl`: routed source
  reads through `std.io_runtime.file_read`.
- `test/01_unit/compiler_shared/diagnostics/{span,severity,label,diagnostic}_spec.spl`:
  routed diagnostics source reads through `std.io_runtime.file_read`.
- `test/01_unit/compiler_shared/diagnostics/label_spec.spl`: replaced an
  expected string containing `{self...}` interpolation with concrete substring
  assertions so the spec checks source text without resolving `self`.
- `test/01_unit/compiler_core/{types,type_subst,traits,traits_module}_spec.spl`:
  routed compiler-core source reads through `std.io_runtime.file_read`; kept
  imports at top level because imports nested inside `describe` do not bind the
  helper for these specs.
- `src/lib/editor/core/{workspace,wal,recovery,recent}.spl` and
  `src/lib/editor/extensions/manifest.spl`: routed host file/process helpers
  through `std.io_runtime` and removed direct `rt_*` extern declarations.
- `src/lib/editor/00.common/{config,keybindings}.spl`,
  `src/lib/editor/core/document.spl`, and `src/lib/editor/buffer/buffer.spl`:
  routed editor file persistence through `std.io_runtime` and removed direct
  `rt_file_*` extern declarations.
- `src/lib/nogc_sync_mut/io_runtime.spl` and `src/lib/io_runtime.spl`: added
  the missing `dir_walk` provider wrapper/export so editor callers do not need
  direct `rt_dir_walk` declarations.
- `src/lib/editor/unified/{unified_backend,project_navigator}.spl`,
  `src/lib/editor/services/{file_watcher,search,md_search}.spl`, and
  `src/lib/editor/extensions/host.spl`: removed direct editor file/directory
  `rt_*` use where `std.io_runtime` now covers it.
- `test/01_unit/lib/editor/extension_discovery_contract_spec.spl` and
  `test/03_system/gui/editor_extension_spec.spl`: routed source/evidence file
  reads through `std.io_runtime` and updated expectations for the wrapper-based
  extension host.
- `test/02_integration/simpleos_driver_log_smoke_spec.spl`: routed driver source
  reads through `std.io_runtime.file_read` and updated the stale source path to
  `src/lib/nogc_sync_mut/driver/null_block_driver.spl`.
- `test/03_system/lib/pure_simple_ssh_https_servers/pure_simple_server_release_smoke_spec.spl`:
  routed the release smoke subprocess through `std.io_runtime.process_run`.
- `test/05_perf/cli_dispatch_perf_spec.spl`: removed duplicated direct
  `rt_time_now_unix_micros`, process, env, and file extern wrappers in favor of
  `std.io_runtime`. Raw scan is clean, but the focused perf spec still reports
  one failing benchmark; tracked in
  `doc/08_tracking/bug/cli_dispatch_perf_spec_failure_2026-06-21.md`.
- `test/05_perf/ctype/{global_static_array_smoke,bench_ctype_static_lut}.spl`:
  routed timer/exit helpers through `std.io_runtime`; fixed the benchmark-local
  table module exports in `test/05_perf/ctype/ctype_lut_tables.spl`. Tracked in
  `doc/08_tracking/bug/ctype_static_lut_export_fix_2026-06-21.md`.
- `src/lib/sdn/__init__.spl`: routed `parse_file` through
  `std.io_runtime.file_read` instead of declaring `rt_file_read_text`.
- `src/lib/scv/wasm_executor.spl`: routed the `SCV_FORCE_FALLBACK` environment
  probe through `std.io_runtime.env_get`.
- `src/app/pkg/manifest.spl`: routed package manifest file existence/read checks
  through `std.io_runtime` and removed stale unused `std.sdn` imports exposed by
  the focused check.
- `test/03_system/check/{html_css_sspec_traceability,html_css_rendering_manifest_traceability}_spec.spl`:
  routed shell execution and evidence/report file reads through `std.io_runtime`.
- `test/01_unit/compiler_core/{traits_extended,traits_compiles,tokens,new_tokens}_spec.spl`:
  routed compiler source reads through `std.io_runtime.file_read`.
- `test/01_unit/compiler_core/{pragma_msg,lang_basics,receive,tmp_test,keyof_token,must_use}_spec.spl`,
  `test/01_unit/compiler_core/entity/{entity_structure,entity_span}_spec.spl`,
  and `test/01_unit/compiler_core/interpreter/{value,ops,jit}_spec.spl`:
  routed compiler source reads through `std.io_runtime.file_read`; focused raw
  scans were clean, all 11 specs passed, and docgen completed with 0 stubs.
- `test/03_system/gui/editor_markdown_spec.spl`: routed source reads through
  `std.io_runtime.file_read`; baseline was green, focused raw scan stayed clean,
  the spec passed after the edit, and docgen completed with 0 stubs.
- `test/03_system/tools/deploy/smoke_spec.spl`: routed deployment smoke file
  existence checks through `std.io_runtime.file_exists`; baseline and post-edit
  focused specs passed, raw scan was clean, and docgen completed with 0 stubs.
- `test/02_integration/os/port/runtime_bundle_policy_spec.spl`: routed source
  reads through `std.io_runtime.file_read`; baseline and post-edit focused
  specs passed, raw scan was clean, and docgen completed with 0 stubs.
- `test/02_integration/os/port/native_convergence_spec.spl`: routed the
  `SIMPLEOS_RUNTIME` environment read through `std.io_runtime.env_get`;
  baseline and post-edit focused specs passed, raw scan was clean, and docgen
  completed with 0 stubs.
- `test/02_integration/os/port/bootstrap_seed_fallback_policy_spec.spl`: routed
  source reads and the seed-wrapper existence check through `std.io_runtime`;
  baseline and post-edit focused specs passed, raw scan was clean, and docgen
  completed with 0 stubs.
- `test/02_integration/os/port/bootstrap_cross_status_spec.spl`: routed source
  reads through `std.io_runtime.file_read`; baseline and post-edit focused
  specs passed, raw scan was clean, and docgen completed with 0 stubs.
- `test/02_integration/os/port/disk_image_bake_spec.spl`: routed static source
  reads through `std.io_runtime.file_read`; baseline and post-edit focused
  specs passed, raw scan was clean, and docgen completed with 0 stubs.
- `test/03_system/tools/simple_lsp_protocol_live_spec.spl`: routed the live
  protocol smoke subprocess through `std.io_runtime.process_run`; baseline and
  post-edit focused specs passed, raw scan was clean, and docgen completed with
  0 stubs.
- `test/03_system/tools/nvim_plugin_live_spec.spl`: routed the plugin smoke
  subprocess through `std.io_runtime.process_run`; baseline and post-edit
  focused specs passed, raw scan was clean, and docgen completed with 0 stubs.
- `test/03_system/tools/bootstrap_mcp_spec.spl`: removed unused file/env runtime
  externs and routed subprocess calls through `std.io_runtime.process_run`;
  baseline and post-edit focused specs passed, raw scan was clean, and docgen
  completed with 0 stubs.
- `test/03_system/tools/test_daemon/test_daemon_flow_system_spec.spl`: routed
  file, directory, pid, and timer host helpers through `std.io_runtime`;
  baseline and post-edit focused specs passed, raw scan was clean, and docgen
  completed with 0 stubs.
- `test/03_system/tools/test_daemon/test_daemon_concurrent_spec.spl`: routed
  file, directory, pid, and timer host helpers through `std.io_runtime`;
  baseline and post-edit focused specs passed, raw scan was clean, and docgen
  completed with 0 stubs.

## Rejected Inline Cleanups

- `test/02_integration/simple_launcher_dispatch_spec.spl`: wrapper conversion
  changed launcher-copy semantics; left unchanged.
- `test/02_integration/app/diff_log_modes_spec.spl`: left unchanged after the
  focused spec failed in current state even with the attempted edit reverted.
- `test/02_integration/ffi_gen/math_migration_test.spl`: left unchanged after
  the focused spec failed under both default and `SIMPLE_LIB=src` runs; not a
  safe inline cleanup.
- `test/03_system/compiler/{import_c_match,struct_reorder}_spec.spl`: left
  unchanged because current source expectations are stale and the focused specs
  fail independently of the runtime-boundary wrapper swap.
- `test/03_system/gui/editor_md_wiki_index_spec.spl`: left unchanged because
  the focused spec is already failing before any runtime-boundary edit.
- `test/02_integration/storage/dbfs/mem_block_device_spec.spl` and
  `test/03_system/compiler/compiler_interpret_pipeline_spec.spl`: left
  unchanged because focused baseline runs are already failing before any
  runtime-boundary edit.
- `test/03_system/tools/repl/{repl_basic_eval,repl_commands,repl_multiline,repl_error_recovery,repl_state_persistence}_system_spec.spl`:
  left unchanged because sampled focused baseline runs failed before any
  runtime-boundary edit.
- `test/03_system/tools/lsp/*_spec.spl` and
  `test/03_system/tools/lint/*_spec.spl`: left unchanged in this pass because
  sampled focused baseline runs timed out before any runtime-boundary edit.
