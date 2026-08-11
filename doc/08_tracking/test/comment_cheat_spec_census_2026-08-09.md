# Comment-Cheat Spec Census (stream I2, 2026-08-09)

Specs whose source-scanning assertion passes ONLY because the needle appears in a
COMMENT line of the product file, never in real code.

## Method

- Corpus: `test/**/*.spl` containing both a product-path literal (`"src/..."`, `"scripts/..."`, ...)
  and a text assertion (`to_contain("...")` / `.contains("...")`). 1,768 candidate spec files.
- Each needle is paired with the nearest preceding product-path literal in the same spec,
  then located in that product file. A hit is CODE unless its line, trimmed, starts with
  `#`, `//`, `*`, or `/*`.
- Scanner validated against the proven H2 case (`editor_gui_spec.spl` ->
  `src/app/editor/main.spl` lines 6-7): reproduced exactly.
- Exhaustive scans used `/usr/bin/grep` (the wrapped `grep` honours .gitignore and undercounts).

## Results

| verdict | raw sites | deduped sites |
|---|---|---|
| CODE (needle is real code) | 11,936 | 8,316 |
| BOTH (code + comment) | 360 | 199 |
| **COMMENT_ONLY (hollow)** | **183** | **108** |
| ABSENT (see caveat) | 16,584 | 12,024 |

Dedup collapses the duplicate spec trees (`test/03_system/` = `test/system/`,
`test/01_unit/` = `test/unit/`) and the generated `.spipe_matchers_*` /
`.spipe_wrapped_entry_*` wrappers by spec basename.

**ABSENT caveat:** the nearest-preceding-path pairing mis-associates needles in specs that
read several product files, so ABSENT is an artifact of the heuristic, NOT a finding. Only
CODE / BOTH / COMMENT_ONLY (where the needle was actually located in the paired file) are
load-bearing. Code-vs-comment split among *located* needles: 8,316 code / 199 both /
108 comment-only = **1.3% hollow**.

## Hollow sites (deduped, 108)

| spec (basename) | needle | product file | comment line(s) |
|---|---|---|---|
| `annotation_intrinsics_spec.spl` | `__builtin_file` | `src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl` | 223 |
| `annotation_intrinsics_spec.spl` | `@file` | `src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl` | 223,253 |
| `annotation_intrinsics_spec.spl` | `@function` | `src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl` | 223,253 |
| `annotation_intrinsics_spec.spl` | `@line` | `src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl` | 223,253 |
| `arm64_user_exit_return_contract_spec.spl` | `nested kernel resume frames` | `src/os/kernel/arch/arm64/user_entry.spl` | 69 |
| `arm64_user_exit_return_contract_spec.spl` | `one active EL0 handoff per CPU` | `src/os/kernel/arch/arm64/user_entry.spl` | 68 |
| `arm64_user_exit_return_contract_spec.spl` | `PID-keyed recorded handoffs` | `src/os/kernel/arch/arm64/user_entry.spl` | 68 |
| `bootstrap_main_source_spec.spl` | `bootstrap_main` | `src/compiler/70.backend/backend/llvm_native_link.spl` | 1132,1154 |
| `bootstrap_main_source_spec.spl` | `rt_native_build` | `src/compiler/70.backend/backend/llvm_native_link.spl` | 1133,1134,1148 |
| `check_entry_target_routing_contract_spec.spl` | `a source` | `src/app/cli/check_entry.spl` | 73 |
| `cli_native_build_main_contract_spec.spl` | `# native-build: pass raw args directly` | `src/app/cli/_CliMain/main_and_help.spl` | 236 |
| `command_dispatch_spec.spl` | `compile` | `src/app/cli/lint_entry.spl` | 4 |
| `concurrency_api_misuse_spec.spl` | `E-PAR-002: numbered-suffix concurrency alias` | `src/compiler/35.semantics/lint/concurrency_api_misuse.spl` | 8 |
| `concurrency_api_misuse_spec.spl` | `E-PAR-003: concurrency symbol imported from wrong module surface` | `src/compiler/35.semantics/lint/concurrency_api_misuse.spl` | 9 |
| `concurrency_api_misuse_spec.spl` | `E-PAR-005: direct use of internal rt_pool_* extern symbols outside the facade` | `src/compiler/35.semantics/lint/concurrency_api_misuse.spl` | 11 |
| `concurrency_api_misuse_spec.spl` | `Rule intents (from Rust seed` | `src/compiler/35.semantics/lint/concurrency_api_misuse.spl` | 13 |
| `context_ponytail_mimic_spec.spl` | `Public absence-rendering gate` | `scripts/check/check-llm-tooling-public-absence-rendering.shs` | 2 |
| `core_c_bootstrap_runtime_capsule_contract_spec.spl` | `bin/` | `scripts/check/build-core-c-bootstrap-runtime-capsule.shs` | 1 |
| `cpu_hotloop_gate_spec.spl` | `cpu-lane-loop-ok` | `scripts/check/check-cpu-hotloop-idiom.shs` | 9,63,249 |
| `cpu_hotloop_gate_spec.spl` | `recursion` | `scripts/check/check-cpu-hotloop-idiom.shs` | 59,313 |
| `cpu_simd_engine2d_simple_bin_spec.spl` | `__riscv_vector` | `src/runtime/runtime_simd_dispatch.c` | 657,871,939 |
| `cross_build_plan_spec.spl` | `cross-` | `src/compiler/90.tools/verify/cross_builds.spl` | 1,3 |
| `database_test_extended_spec.spl` | `Test Database Extended - Main Module` | `src/lib/nogc_sync_mut/database/test_extended.spl` | 1 |
| `database_test_extended_spec.spl` | `timing_runs` | `src/lib/nogc_sync_mut/database/test_extended.spl` | 4 |
| `editor_buffer_spec.spl` | `editor_tui_run(session)` | `src/app/editor/main.spl` | 7 |
| `editor_dock_zone_spec.spl` | `spl` | `src/lib/editor/view/status_bar_indicators.spl` | 3 |
| `editor_gui_sdl_spec.spl` | `gui_sdl_bridge` | `src/lib/editor/70.backend/gui_sdl_bridge.spl` | 1 |
| `editor_gui_spec.spl` | `editor_tui_run(session)` | `src/app/editor/main.spl` | 7 |
| `editor_gui_spec.spl` | `gui_shell_run(session)` | `src/app/editor/main.spl` | 6 |
| `editor_md_language_spec.spl` | `char_at` | `src/lib/editor/extensions/builtin/md_language.spl` | 62 |
| `engine2d_gpu_offload_contract_spec.spl` | `SIMPLE_GUI_BACKEND` | `src/os/compositor/host_compositor_core.spl` | 1509 |
| `entity_span_spec.spl` | `# This is the CANONICAL Span definition for the entire compiler.` | `src/compiler/00.common/diagnostics/span.spl` | 4 |
| `entry_closure_physical_source_dedup_spec.spl` | `# An explicit-entry walk is a closure even when import resolution` | `src/compiler/80.driver/driver_source_pipeline_loading.spl` | 259 |
| `evalops_export_and_text_at_spec.spl` | `bounds-checked Option accessor` | `src/compiler/10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl` | 303 |
| `evalops_export_and_text_at_spec.spl` | `interpreter_method/string.rs` | `src/compiler/10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl` | 59,295 |
| `evalops_export_and_text_at_spec.spl` | `rt_string_char_at` | `src/compiler/10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl` | 271,297,310 |
| `file_class_introspection_spec.spl` | `.class -> __traits("class_info", "TypeName")` | `src/compiler/10.frontend/core/parser_expr.spl` | 948,1155 |
| `file_class_introspection_spec.spl` | `.FILE -> __traits("module_file", "dotted.path")` | `src/compiler/10.frontend/core/parser_expr.spl` | 936,1143 |
| `file_class_introspection_spec.spl` | `.* -> __traits("module_wildcard", "dotted.prefix")` | `src/compiler/10.frontend/core/parser_expr.spl` | 960,1167 |
| `fork_alloc_tracking_spec.spl` | `#define FORK_CAPTURE_LIMIT (4U * 1024U * 1024U)` | `src/runtime/runtime_fork.c` | 74 |
| `fork_alloc_tracking_spec.spl` | `#include "runtime_memtrack.h"` | `src/runtime/runtime_fork.c` | 50 |
| `generic_syntax_spec.spl` | `Check for generic type: Option<T>, Result<T, E>, Dict<K,V>, etc.` | `src/compiler/10.frontend/core/parser.spl` | 672 |
| `ghdl_riscv32_mailbox_spec.spl` | `ghdl_mailbox_runner` | `src/lib/nogc_async_mut_noalloc/baremetal/ghdl_mailbox_runner.shs` | 7 |
| `gui_showcase_perf_artifact_provenance_contract_spec.spl` | `*) SIMPLE_BIN_SOURCE="repo-bin"` | `scripts/check/check-widget-showcase-4k-200fps.shs` | 38 |
| `ignored_return_warning_spec.spl` | `Check if this is a function call with ignored return value` | `src/compiler/10.frontend/core/interpreter/eval_stmts.spl` | 131 |
| `jupyter_kernel_export_comm_spec.spl` | `"status":"ok"` | `src/app/jupyter_kernel/main.spl` | 411 |
| `keyof_spec.spl` | `# ## keyof Operator` | `src/lib/nogc_sync_mut/intrinsics.spl` | 53 |
| `keyof_spec.spl` | `# keyof T -- compile-time field name list` | `src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl` | 257 |
| `keyof_spec.spl` | `#   keyof T` | `src/lib/nogc_sync_mut/intrinsics.spl` | 55 |
| `macos_gui_live_window_gate_source_spec.spl` | `<file.spl|file.smf>` | `scripts/gui/macos-gui-run.shs` | 12 |
| `macos_gui_live_window_gate_source_spec.spl` | `*.spl|*.smf` | `scripts/gui/macos-gui-run.shs` | 72 |
| `macos_metal_live_evidence_contract_spec.spl` | `invalid-backend` | `scripts/check/check-macos-gpu-2d-live-evidence.shs` | 10 |
| `mcp_analysis_tools_spec.spl` | `src/` | `src/app/cli/main.spl` | 14 |
| `mcp_debug_log_spec.spl` | `debuglog://` | `src/lib/nogc_async_mut/mcp/debug_log_tools.spl` | 291 |
| `mcp_lsp_tools_spec.spl` | `bin/simple query` | `src/app/cli/query.spl` | 5 |
| `mixin_expr_spec.spl` | `mixin(code_text) -- compile-time code generation` | `src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl` | 269 |
| `native_build_cache_plumbing_spec.spl` | `Byl` | `src/compiler/70.backend/backend_types.spl` | 33 |
| `native_build_cache_plumbing_spec.spl` | `Compiler` | `src/compiler/70.backend/backend_types.spl` | 88 |
| `packed_struct_bitfield_spec.spl` | `T:N syntax` | `src/compiler/10.frontend/core/_ParserDecls/fn_struct_decls.spl` | 1027 |
| `platform_capsule_spec.spl` | `platform` | `src/os/kernel/arch/riscv64/platform/manifest.spl` | 1 |
| `platform_capsule_spec.spl` | `platform` | `src/os/kernel/arch/riscv64/platform/timer_mmio.spl` | 1 |
| `platform_capsule_spec.spl` | `platform` | `src/os/kernel/arch/riscv64/platform/uart_mmio.spl` | 1 |
| `platform_capsule_spec.spl` | `riscv64` | `src/os/kernel/arch/riscv64/platform/timer_mmio.spl` | 6 |
| `pragma_msg_spec.spl` | `pragma_msg(expr)` | `src/compiler/10.frontend/core/interpreter/eval_builtins.spl` | 158 |
| `preprocess_conditionals_spec.spl` | `Keep line count stable for diagnostics` | `src/compiler/10.frontend/core/parser_preprocessor.spl` | 361 |
| `processing_cuda_backend_spec.spl` | `A caller-supplied --entry is authoritative` | `src/compiler/80.driver/driver_source_loading.spl` | 52 |
| `qemu_runner_spec.spl` | `build/os/generated` | `src/os/kernel/arch/riscv64/boot.spl` | 47,49 |
| `qemu_runner_spec.spl` | `--entry-closure` | `src/os/kernel/arch/riscv64/boot.spl` | 22 |
| `qemu_runner_spec.spl` | `--entry` | `src/os/kernel/arch/riscv64/boot.spl` | 22 |
| `qemu_runner_spec.spl` | `-kernel` | `src/os/kernel/arch/arm32/boot.spl` | 12,38 |
| `qemu_runner_spec.spl` | `-kernel` | `src/os/kernel/arch/riscv64/boot.spl` | 48 |
| `qemu_runner_spec.spl` | `src/lib` | `src/os/kernel/arch/riscv64/boot.spl` | 49 |
| `qemu_runner_spec.spl` | `src/os` | `src/os/kernel/arch/riscv64/boot.spl` | 49 |
| `riscv32_boot_qemu_spec.spl` | `RISC-V 32` | `src/os/kernel/arch/riscv32/boot.spl` | 1 |
| `riscv_product_ports_source_spec.spl` | `DTB bytes and memory images belong to the SoC memory owner` | `src/lib/hardware/rv64gc_rtl/imac_entry.spl` | 3 |
| `runtime_surface_spec.spl` | `compiler.loader.runtime` | `src/compiler/99.loader/__init__.spl` | 6 |
| `simplebox_build_spec.spl` | `build/os/rootfs/bin/simplebox` | `src/os/tools/simplebox/simplebox_main.spl` | 11 |
| `simplebox_build_spec.spl` | `src/os/tools/simplebox/simplebox_main.spl` | `src/os/tools/simplebox/simplebox_main.spl` | 11 |
| `simpleos_crypto_random_gate_spec.spl` | `cycle+time+instret` | `src/os/kernel/arch/riscv64/entropy.spl` | 17 |
| `simpleos_crypto_random_gate_spec.spl` | `RISC-V TLS remains blocked` | `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` | 3329 |
| `simpleos_green_hardware_handoff_blocker_spec.spl` | `rt_syscall_dispatch` | `src/os/kernel/ipc/syscall.spl` | 206 |
| `simpleos_riscv_network_gate_spec.spl` | `#define RT_PCI_MAX_DEVICES 32` | `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` | 1657 |
| `simpleos_riscv_network_gate_spec.spl` | `rt_storage_probe_nvfs_arena_payload` | `scripts/qemu/qemu_rv64_http_test.shs` | 161 |
| `simpleos_wm_fullscreen_evidence_simple_bin_spec.spl` | `bootstrap*seed` | `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` | 802 |
| `simpleos_wm_fullscreen_evidence_simple_bin_spec.spl` | `rust-built` | `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` | 802 |
| `simpleos_wm_fullscreen_evidence_simple_bin_spec.spl` | `rust*seed` | `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` | 802 |
| `simple_sdl3_contract_spec.spl` | `SDL3_EVENT_KEY_DOWN UINT32_C(0x300)` | `src/runtime/runtime_sdl3.c` | 30 |
| `simple_sdl3_contract_spec.spl` | `SDL3_EVENT_MOUSE_MOTION UINT32_C(0x400)` | `src/runtime/runtime_sdl3.c` | 33 |
| `stage4_memory_gate_spec.spl` | `<unattributed>` | `src/app/memstat/main.spl` | 20,141 |
| `star_export_lint_spec.spl` | `Star wildcard warnings` | `src/app/cli/query_lint.spl` | 707 |
| `stdlib_intensive_spec.spl` | `name` | `src/compiler/10.frontend/core/lexer.spl` | 69 |
| `sugar_plugin_spec.spl` | `# Pow and unsupported future ops still use the scalar fallback.` | `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl` | 1120 |
| `sugar_plugin_spec.spl` | `[STATIC-NEXT] sugar rule registry` | `src/compiler/70.backend/backend/_CBackendTranslate/class_core.spl` | 432 |
| `tensor_dimensions_spec.spl` | `Tensor Dimension` | `src/compiler_rust/lib/std/src/verification/regenerate/tensor_dimensions.spl` | 1 |
| `test_runner_bounded_output_contract_spec.spl` | `#define FORK_CAPTURE_LIMIT (4U * 1024U * 1024U)` | `src/runtime/runtime_fork.c` | 74 |
| `thread_alloc_tracking_spec.spl` | `#include "runtime_memtrack.h"` | `src/runtime/runtime_thread.c` | 13 |
| `trait_desugar_spec.spl` | `struct Name:` | `src/app/desugar/trait_desugar.spl` | 7 |
| `trait_desugar_spec.spl` | `trait Name:` | `src/app/desugar/trait_desugar.spl` | 7 |
| `traits_spec.spl` | `@traits(query, T, ...) desugars to __traits` | `src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl` | 222 |
| `wm_host_freebsd_refusal_spec.spl` | `host.spl` | `src/os/compositor/hosted_input_backend.spl` | 5 |
| `wm_multiapp_taskbar_spec.spl` | `[wm-multiapp] final_state_ready` | `scripts/check/check-wm-multiapp-taskbar-evidence.shs` | 20 |
| `wm_multiapp_taskbar_spec.spl` | `[wm-multiapp] launched app=` | `scripts/check/check-wm-multiapp-taskbar-evidence.shs` | 13 |
| `wm_multiapp_taskbar_spec.spl` | `[wm-multiapp] minimized id=` | `scripts/check/check-wm-multiapp-taskbar-evidence.shs` | 17 |
| `wm_multiapp_taskbar_spec.spl` | `[wm-multiapp] taskbar_focus ` | `scripts/check/check-wm-multiapp-taskbar-evidence.shs` | 15 |
| `wm_multiapp_taskbar_spec.spl` | `[wm-multiapp] taskbar_restore ` | `scripts/check/check-wm-multiapp-taskbar-evidence.shs` | 18 |
| `ws_e2e_spec.spl` | `bearer ` | `src/app/ui.web/session_token.spl` | 1 |
| `x25519mlkem768_absolute_spec.spl` | `version` | `src/runtime/runtime_simd_dispatch.c` | 298 |
| `x86_64_fs_exec_spawn_spec.spl` | `AT_EXECFN` | `src/os/kernel/loader/x86_64_fs_exec_ring3.spl` | 134 |

## Worst offenders (most hollow needles in one spec)

| spec | hollow needles |
|---|---|
| `qemu_runner_spec.spl` | 7 |
| `wm_multiapp_taskbar_spec.spl` | 5 |
| `platform_capsule_spec.spl` | 4 |
| `concurrency_api_misuse_spec.spl` | 4 |
| `annotation_intrinsics_spec.spl` | 4 |
| `simpleos_wm_fullscreen_evidence_simple_bin_spec.spl` | 3 |
| `keyof_spec.spl` | 3 |
| `file_class_introspection_spec.spl` | 3 |
| `evalops_export_and_text_at_spec.spl` | 3 |
| `arm64_user_exit_return_contract_spec.spl` | 3 |
| `trait_desugar_spec.spl` | 2 |
| `sugar_plugin_spec.spl` | 2 |

## Fix guidance

- The honest fix is to **anchor the needle to real syntax** (e.g. assert on
  `fn gui_shell_run(` at its definition site, or on the call expression plus its
  surrounding dispatch keyword), not to delete the assertion and never to relax it.
- Better still: replace source-grep assertions with behavioural ones where a runnable
  path exists. A needle that can match a comment proves nothing about behaviour.
- Nothing was fixed by this pass; it is enumeration only.

---

## Remediation status (stream K4, 2026-08-10)

Landed as `4e83c9abaf8`, `8d0f432102c`, `f2bcadfc51c`. Method: anchor each needle
to real declaration/dispatch syntax so a comment cannot satisfy it. No needle was
relaxed; nothing was dropped without an equal-or-stronger real-code replacement.
Every replacement needle was pre-checked to exist in the product file on a
non-comment line before the spec was run.

### FIXED — 43 sites / 28 specs

`annotation_intrinsics` (4), `concurrency_api_misuse` (4), `platform_capsule` (4),
`keyof` (3), `file_class_introspection` (3), `trait_desugar` (2),
`native_build_cache_plumbing` (2), `editor_gui` (2), and one site each in
`pragma_msg`, `mixin_expr`, `traits`, `packed_struct_bitfield`, `generic_syntax`,
`ignored_return_warning`, `preprocess_conditionals`, `entity_span`,
`star_export_lint`, `runtime_surface`, `check_entry_target_routing_contract`,
`cross_build_plan`, `database_test_extended`, `mcp_debug_log`, `editor_buffer`,
`editor_gui_sdl`, `editor_md_language`, `cli_native_build_main_contract`,
`entry_closure_physical_source_dedup`, `processing_cuda_backend`.

Duplicate-tree copies were fixed in lockstep where they carried the same needle
(`test/system/...`, `test/unit/...`); several duplicates turned out to be pending
stubs and needed no change.

### NEWLY RED — 1 real defect the hollow needles were hiding

`editor_gui_spec.spl` + `editor_buffer_spec.spl`: `src/app/editor/main.spl`
advertises `--gui` in `print_help()` but has no dispatch arm for it, and never
calls `editor_tui_run`. Both needles matched only main.spl:6-7, a comment calling
those calls "the intended dispatch hooks". Filed as
`doc/08_tracking/bug/editor_main_gui_and_tui_dispatch_missing_2026-08-10.md`;
the specs are LEFT RED.

Two other specs were STALE rather than defective and were repointed:
`editor_md_language` (`char_at` replaced by a byte slice in the product; only the
change-log comment still mentions it) and `cli_native_build_main_contract`.

### NOT A FINDING — 7 sites (deliberate pins / heuristic mis-pairs)

- `sugar_plugin_spec.spl` (2): the `[STATIC-NEXT]` marker contract asserts that
  marker COMMENTS exist at three named sites. Asserting a comment IS the contract.
- `evalops_export_and_text_at_spec.spl` (3): an `it` block explicitly named
  "documents text .at as a deliberate divergence from the seed" pins the rationale
  comment on purpose, inside an `arm_body`-bounded slice.
- `stdlib_intensive_spec.spl` (1): the needle is spec-internal control flow
  (`if line.contains("name"):  # Skip header`), not an assertion.
- `database_test_extended_spec.spl` `timing_runs`: real code in
  `test_extended/database.spl:66`; the census paired it with the wrong file.

`mcp_analysis_tools_spec.spl` and `mcp_lsp_tools_spec.spl` are a different and
worse defect than comment-cheating: they build the string under test inside the
spec and then assert against it, so they never read the product at all. Out of
scope here; they need rewriting, not anchoring.

### REMAINING — 46 sites

Everything in the table above not listed as FIXED or NOT A FINDING, minus the 12
sites in `qemu_runner_spec.spl` (7) and `wm_multiapp_taskbar_spec.spl` (5), which
stream J2 owned concurrently. The bulk of the remainder is SimpleOS / QEMU /
GUI-evidence shell-script gates (`simpleos_*`, `macos_*`, `wm_host_*`,
`cpu_hotloop_gate`, `gui_showcase_perf_*`), which need a runnable-evidence review
rather than a syntax anchor.

### Anchoring pitfall: `{...}` in a needle is INTERPOLATION, not text

Anyone continuing this work will hit this immediately, because real product code
is full of interpolated strings and `use mod.{A, B}` imports — exactly the lines
you most want to anchor on.

A matched `{...}` pair inside a Simple text literal is **string interpolation**.
A source-grep needle containing one never becomes the literal text it appears to
be, and it fails in one of two silent ways:

- the name is not in scope → the whole `it` block dies with
  `semantic: variable 'X' not found` **before reaching any assertion**;
- the name IS in scope → the needle silently becomes different text, and the
  assertion tests something nobody wrote.

Write `{{` / `}}`, which render as literal `{` / `}` (verified against the
bootstrap binary). An unmatched opening brace (`...compiler_sffi.{`) is also
safe, but the doubled form keeps the needle readable and complete.

This was already live in the corpus before this campaign:
`runtime_surface_spec.spl`'s "runtime facade keeps the curated export list"
example contained `module_loader.{moduleloader_execute_smf}` and had therefore
**never executed a single assertion** — it aborted on the unresolved name every
run. Worth a dedicated sweep: `grep -nE '^\s*(expect|check)\(' test/**/*.spl |
grep -E '[^{]\{[A-Za-z_][A-Za-z0-9_]*\}[^}]'`.
