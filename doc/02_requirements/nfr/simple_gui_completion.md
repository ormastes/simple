# Non-Functional Requirements: Simple GUI Completion (`release/1.0.0`)

- **Date:** 2026-11-28
- **Status:** Approved by User (Option 1)
- **Target Branch:** `release/1.0.0` (never `main`)
- **Worktree:** `/Users/ormastes/work/web_2d_gui_gui` (`work/simple-gui-complete`)

## Selected NFR Targets: Balanced Release Quality

| ID | Quality Attribute | Requirement / Target | Verification Mechanism |
|---|---|---|---|
| `NFR-SGUI-001` | Incremental Retained Damage | Local events (clock ticks, single-window updates, window moves) produce `DAMAGE_PLAN_LOCAL` without full-frame repaint, including parent-sampling glass themes (`fluid_light`, `aetheric_dark`), pixel-exact vs fresh full-frame render. | `wm_retained_clock_tick_spec`, `wm_retained_parent_sampling_damage_spec`, `engine2d_wm_local_lane_clock_tick_spec` |
| `NFR-SGUI-002` | Deterministic Focus & Input Routing | Focus traversal, pointer hit-testing, pointer capture, and IME/key dispatch are deterministic, prefix-isolated across specs, and respect visibility, enabled state, and `z_order`. | `focus_tab_index_spec`, `widget_hit_spec`, `widget_text_edit_spec`, `showcase_core_spec` |
| `NFR-SGUI-003` | HiDPI Scale Integrity | Logical layout dimensions match `dev / scale`, backing buffers match exact physical `inner_size()`, and `GUI_EVT_SCALE_CHANGED` invalidates retained caches and updates scale without restart. | `host_gui_device_scale_spec` + dynamic scale-change tests |
| `NFR-SGUI-004` | Zero Silent Skipped Specs | No spec passes vacuously via missing imports, empty bodies, `pass_todo`, or silent GPU/macOS fallbacks; environment-gated checks emit explicit receipts or fail closed. | `macos_gui_live_window_evidence_spec`, `showcase_hosts_spec`, `engine2d_gpu_offload_contract_spec` |
| `NFR-SGUI-005` | Trait & Boundary Compatibility | `ScreenHost` remains strictly additive over `RenderBackend` (all 8 `RenderBackend` importers unchanged), and modules obey `direct-env-runtime-guard` and backend-isolation rules. | `simple check` + `scripts/audit/direct-env-runtime-guard.shs` |
