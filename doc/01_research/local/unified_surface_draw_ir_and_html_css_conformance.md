<!-- codex-research -->
# Local Research — Unified Surface Lowering and HTML/CSS Conformance

Date: 2026-07-29
Status: research complete; requirement choice pending

## Requested outcome

Unify Simple 2D, GUI, Web, UI, graphical TUI, and graphical CLI rendering behind
the existing Draw IR executor; preserve optimized producer-owned structures;
remove duplicate paint logic without breaking compatibility; then complete HTML
and CSS through modern executable SSpec coverage derived from standards.

## Existing ownership

| Layer | Existing owner | Current lowering |
|---|---|---|
| Shared execution display list | `src/lib/common/ui/draw_ir.spl` | `DrawIrComposition` schema `simple-draw-ir-v2` |
| Engine execution | `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl` | Draw IR to Engine2D/backend material |
| Web semantic/layout | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer*.spl` | private HTML/CSS nodes, styles, and boxes to Draw IR |
| GUI widgets | `src/lib/common/ui/widget_draw_ir.spl` | laid-out `WidgetNode` to Draw IR |
| Window manager | `src/lib/common/ui/window_scene_draw_ir.spl` | `SharedWmScene` to Draw IR |
| Simple 2D | `Simple2dDrawIrPlan` in `draw_ir.spl` | manual Draw IR to shared executor |
| Inspection/incremental update | `draw_ir_diff.spl`, `draw_ir_patch.spl` | composition diff/patch without backend state |

`DrawIrSourceInfo.source_kind` already distinguishes `manual`, `gui_ast`,
`html_ast`, and `wm_scene`. It preserves producer identity without changing
command execution.

## Existing decisions that constrain the plan

- `doc/03_plan/ui/webir_drawir_optimization.md` explicitly rejects a second
  public `WebIrDocument` display list. “WebIR” names private web
  semantic/layout state; `DrawIrComposition` is the shared display list.
- `doc/04_architecture/ui/simple_gui_stack.md` requires HTML/CSS and GUI style
  resolution before Draw IR. Executors must not parse HTML/CSS or infer layout.
- GUI/Web/WM text must use Draw IR `draw_text`; font faces, atlases, caches, and
  GPU resources stay transient inside Engine2D.
- `draw_ir_diff.spl` and `draw_ir_patch.spl` already provide the reusable
  incremental boundary. A parallel per-producer diff format would duplicate it.

## Duplication and compatibility risks

1. Public `WebIr`, `GuiIr`, `UiIr`, `TuiIr`, and `CliIr` command trees would
   duplicate geometry, clipping, text, image, ordering, provenance, diff, SDN,
   and validation logic already owned by Draw IR.
2. Forcing native CLI output through a pixel display list would lose stream,
   exit-status, pipe, and terminal semantics. CLI should lower to Draw IR only
   for a graphical surface.
3. TUI cells need terminal-specific semantics (cell width, grapheme, ANSI
   state, cursor). Keep a compact cell/grid owner and add a graphical adapter;
   do not make Draw IR the terminal protocol.
4. Web and GUI structures have different hot-path needs. Web needs compact
   cascade/layout records and subtree invalidation; GUI needs retained widget
   identity and event state. One universal semantic node would inflate both.
5. Legacy pixel paths cannot be removed until semantic Draw IR, exact Simple
   pixels, and representative hosted frames agree.

## Existing test state

The inspected web-platform/app system specs already import `std.spec`; a bulk
syntax rewrite is unnecessary. Modernization should instead add:

- REQ traceability and standards-section metadata;
- `step("...")` manual flows and typed `@capture(html)` evidence;
- semantic DOM/computed-style/layout/Draw IR assertions before pixels;
- real production rendering rather than source/status-only success;
- WPT-derived reftest fixtures with explicit match/mismatch or tolerance policy.

`test/03_system/check/html_css_full_rendering_goal_status_spec.spl` currently
reports complete element/inventory accounting separately from incomplete full
CSS rendering. Inventory presence is not behavioral conformance.

## Selected refinement: Vulkan-first UiIr

The requested direction adds one lower execution layer:

```
producer semantic state -> DrawIrComposition -> UiIr -> Vulkan
```

`UiIr` takes the role called `DisplayGraphIR` in
`doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md`. It is derived only
from validated Draw IR and is optimized for upload, batching, dirty regions,
clip/resource indices, and deterministic replay. It does not contain HTML,
CSS, widget, terminal, Vulkan handle, descriptor, pipeline, shader, atlas, or
device-lifetime ownership.

Vulkan is the first executor and performance target. Later Metal/DirectX/CPU
executors consume the same UiIr semantics; they do not cause producer-specific
IR forks.

## Local conclusion

Treat WebIR, GUIIR, TUIIR, and CLIIR as producer-owned semantic models or named
lowering surfaces, not copies of Draw IR. Standardize their boundary as
deterministic `*_to_draw_ir(...) -> DrawIrComposition` functions plus
`DrawIrSourceInfo` provenance. Draw IR remains the stable semantic display
list; the selected `UiIr` is its compact backend-facing execution form,
Vulkan-optimized first.

## Related existing plans

- `doc/03_plan/ui/webir_drawir_optimization.md`
- `doc/03_plan/ui/rendering/draw_ir_multibackend_plan.md`
- `doc/03_plan/ui/web_browser/pure_simple_web_renderer_chromium_quality_plan.md`
- `doc/03_plan/ui/web_browser/simple_browser_chrome_class_roadmap.md`
- `doc/04_architecture/ui/simple_gui_stack.md`
