# Local Research: Simple 2D Primitive Lane

Research date: 2026-08-08. This is a source inventory, not a completion
claim. The repository already has separate host, compositor, browser-layout,
font, and QEMU GPU contracts; the gap is proving one primitive semantic path
across them.

## Current owners found

| Concern | Source owner(s) | Existing evidence surface |
|---|---|---|
| Input/modifiers | `src/lib/common/ui/input_event.spl`, `src/os/gui/input_event.spl` | `test/unit/common/ui/input_event_conformance_spec.spl` |
| GUI/widget activation | `src/app/ui*`, widget/event pipeline | `test/unit/app/ui/widget_button_checkbox_dropdown_spec.spl`, `test/system/gui/event_processing_spec.spl` |
| WM drag/scroll | `src/os/compositor/host_gui_event_router.spl`, `wm_action_applier`, layout owners | `test/unit/os/compositor/wm_action_applier_spec.spl`, `test/system/gui/wm_input_qemu_smoke_spec.spl` |
| Web hit/layout | browser-engine/layout owners | `test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_hit_test_events_spec.spl`, DOM-event and CSS suites |
| Draw IR/2D | common Draw IR, `engine2d_wm_frame_executor`, `src/app/ui_showcase/` | `test/03_system/ui_showcase/showcase_hosts_spec.spl`, game2d and Draw IR integration specs |
| Fonts | `src/lib/gc_sync_mut/text_layout/font_renderer.spl`, vector-font owners | `test/03_system/lib/text_layout/vector_font_pipeline_spec.spl` |
| QEMU GPU | `SimpleOsHostGpuSession` and canonical wrapper | `test/03_system/os/qemu/simpleos_qemu_host_gpu_2d_spec.spl` |

## Gaps to close

1. Host tests must assert the full button/drag/scroll/layout/font state
   transition, not only isolated helper output.
2. GUI, WM, Web, and 2D must consume common event/layout/composition contracts;
   any private duplicate is an architecture defect.
3. Showcase capture must retain semantic events, animation state, text/font
   provenance, device-origin pixels, and exact CPU parity together.
4. QEMU must execute the admitted pure-Simple artifact and retain the complete
   Vulkan receipt; source checks and TCG are narrower evidence.
5. Performance needs 20 post-oracle warm samples, nearest-rank p95, and
   concurrent RSS. No perf claim is inferred from a host-only benchmark.

## Research conclusion

Implement host primitives first, then run the same scenario through each
surface and the canonical QEMU wrapper. Preserve macOS and UNO Q as explicit
deferred rows until their required runtime/board evidence exists.
