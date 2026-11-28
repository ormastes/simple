# Simple GUI Completion — Agent Task Breakdown (`release/1.0.0`)

- **Date:** 2026-11-28
- **Status:** Active Execution Plan
- **Target Branch:** `release/1.0.0`
- **Merge Owner:** Simple GUI Completion Subagent (branching `work/*` off `origin/release/1.0.0`, PR `--base release/1.0.0`)
- **Final Reviewer:** Coordinator / Root Review (`gh pr diff <n>` zero P0/P1 before `--admin --merge`)
- **Lower-Model Sidecars:** `N/A` (executed directly in single isolated worktree `/Users/ormastes/work/web_2d_gui_gui` with sequential single-file test discipline while P4 build runs elsewhere)

---

## Task Lanes & PR Slices

| Slice / PR | Scope | Files Owned | Acceptance Gate |
|---|---|---|---|
| **Slice 1 (PR #1)** | Step 2 Design Docs + Repair 4 broken `backend_factory` / `UnifiedApp` specs (`REQ-SGUI-001`), TinyGUI `metadata_valid()` (`REQ-SGUI-002`), Theme cascade effective var & child-frame admission (`REQ-SGUI-003`) | `doc/04_architecture/simple_gui_completion.md`, `doc/05_design/simple_gui_completion*.md`, `doc/03_plan/*/simple_gui_completion.md`, `test/01_unit/app/ui/{async_default_api_spec,unified_app_spec}.spl`, `test/03_system/gui/{capability_negotiation_spec,unified_app_spec}.spl`, `doc/06_spec/03_system/gui/{capability_negotiation_spec,unified_app_spec}.md`, `src/lib/nogc_sync_mut/tiny/gui/state.spl`, `test/01_unit/lib/tiny/tiny_layout_linear_spec.spl`, `src/app/ui.web/wm_quality_contract.spl`, `src/os/compositor/host_compositor_core.spl`, `test/01_unit/lib/common/ui/wm_full_stack_demo_child_theme_spec.spl` | All Slice 1 specs pass; `RenderBackend` 8 importers untouched; `direct-env-runtime-guard` clean. |
| **Slice 2 (PR #2)** | Focusable filtering & blur (`REQ-SGUI-004`), Pointer capture + `GuiRenderer` shift/text input (`REQ-SGUI-005`), HiDPI `GUI_EVT_SCALE_CHANGED` (`REQ-SGUI-006`), `HostCompositor` pointer/minimize fixes (`REQ-SGUI-010`) | `src/lib/common/ui/event.spl`, `src/lib/common/ui/widget_hit.spl`, `src/lib/nogc_sync_mut/ui/gui_renderer.spl`, `src/app/ui_showcase/hosts/host_gui.spl`, `test/01_unit/lib/common/ui/{focus_tab_index_spec,widget_hit_spec}.spl`, `test/01_unit/app/ui_showcase/host_gui_device_scale_spec.spl`, `test/03_system/ui_showcase/showcase_hosts_spec.spl`, `test/03_system/wm/wm_full_stack_demo_spec.spl` | Focus/blur, pointer capture, `GUI_EVT_SCALE_CHANGED`, `GUI_EVT_TEXT_INPUT`, and `wm_full_stack_demo_spec` 6/6 pass. |
| **Slice 3 (PR #3)** | Retained-damage parent-sampling parity (`REQ-SGUI-007`), Showcase stabilization (`REQ-SGUI-008`), macOS live-window & `DrawIrV3Scene` SSpec gates (`REQ-SGUI-009`) + `doc/06_spec/` manuals | `src/lib/gc_async_mut/ui/gui_content_renderer.spl`, `test/01_unit/lib/gc_async_mut/ui/gui_content_renderer_spec.spl`, `test/03_system/gui/{macos_gui_live_window_evidence_spec,ui_draw_ir_pipeline_spec,engine2d_gpu_offload_contract_spec}.spl`, `doc/06_spec/**` | `gui_content_renderer_spec`, `wm_retained_*_spec`, `showcase_*_spec`, `ui_draw_ir_pipeline_spec`, `macos_gui_live_window_evidence_spec` pass; `find doc/06_spec -name '*_spec.spl' \| wc -l == 0`. |
