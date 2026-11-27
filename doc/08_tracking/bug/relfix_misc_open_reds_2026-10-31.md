# relfix-misc: specs left RED, with reason (2026-10-31)

Stale vs product drift needing an owner decision (not rewritten, to avoid guessing):
- qemu_frozen_source_admission: x86 wm-fullscreen wrapper no longer uses qemu-frozen-source-admission
  (no qemu_admission_begin x86_64 / ensure_generated_log_config in wrapper or lib/simpleos-wm-fullscreen).
- clang_23_1_browser_demo: build_browser_demo_client.shs defaults clang-20, no `make CC=`.
- hosted_wm_capture / wm_gui_window_drawing: producer lost render_crop_ppm_with_metrics.
- draw_ir_web_renderer_vulkan_rect_list_contract: rect_list renamed to rect_batch (backend_vulkan_rect_batch_spirv.spl).
- chrome_modern_web_platform_compat (11 left): br_* functions renamed.
- next_beta_full_bootstrap_simpleos_multiarch, bootstrap_deploy_rollback, macos_*: scripts/workflows changed.
- windows_dangling_symlink_fails_loudly: tracked dangling now always fatal, message text changed.
- semantic_link_lint: reference definition rewritten to spl://pkg/..#fn:.. not spl:fn@..
- ide_office_plugin_suite: src/app/ide/markdown_render.spl hard-codes preview_line_count 0 /
  rendered_line_count 2 behind a Phase-3 ABI workaround; spec asserts >2; line also 127 wide.
- gui_renderdoc_aggregate_cache_modes: Windows absolute path vs relative path expectation.
- DESIGN-SCAFFOLD fail(): spipe_knowledge_compiler_*; mcp_cmdline_handshake (helper undefined, needs Stage 2 build).

ENV-BLOCKED: specs running bin/simple on the seed ("expected WARNING: this Rust-built Simple binary...",
scv_*, gen_lean, requires_range); devhub (DEVHUB_*_BIN unset); mcp stdio ("compiled child requires
nondelegating real execution"); evidence.env produced by absent gates (cross_app_glyph_consistency,
gui_low_res_readability); gpu_tutorial (submodule absent, skip() arity); native-build lanes.

Seed suspects: `variable os not found` in mixed_language_kpf_conformance (use os.tooling... imports);
`variable GdbBreakpoint not found` in gdb_mi_transport (imported, static call across modules).

## test/03_system/app/simple_web/feature/web_font_rendering_surface_spec.spl (0/3, seed on Windows, 2026-10-31)

Run with `build/fix/seed.exe test <spec> --no-session-daemon`: 0 of 3 pass. Three distinct failures:

1. "should submit selected Web text and ordered advances as readable glyphs" fails with
   `semantic: nil is forbidden by the non-optional return contract of 'file_hash_sha256'`.
   `src/lib/nogc_sync_mut/io/file_ops.spl:292` `file_hash_sha256` is declared `-> text` but the seed's
   `rt_file_hash_sha256` (interpreter_extern/file_io.rs:449) returns nil on this host; the
   io_runtime.spl:345 variant falls back to `sha256sum`, file_ops.spl does not. Not a small fix: needs
   an `_or_empty` fallback decision (the comment at io_runtime.spl:~350 says the one-call form must never shell out).
2. "should fail closed when HTML parsing yields no element surface": expected 4608 to equal 0.
3. "should deliver correlated browser focus keyboard pointer timing and animation events":
   `wm_browser_event_routing_reason=missing-simple-web-font-run-id` (a downstream effect of 1, no font run id recorded).

Not fixed here; 2 is unexamined.
