# Bug: layout renderer hits nil.lower() when caller module imports engine2d backends directly

- **Date:** 2026-07-03
- **Severity:** medium (module-init ordering; blocks combining parity + layout lanes in one module)
- **Area:** interpreter module initialization ordering

## Symptom
Routing HTML through simple_web_html_layout_renderer from a module that ALSO
directly imports the engine2d backend modules (backend_metal/opencl/vulkan/
software/cpu + simd_provider) throws a runtime error mid-render:
`method 'lower' not found on nil` — a layout-renderer module global is nil in
that import context. The identical render from a lean-import module works.

## Repro
Observed while adding widget fixtures to
src/app/wm_compare/production_gui_web_renderer_parity.spl (imports the full
backend set): first real-layout render fails with nil.lower(). Moving the
fixtures to a lean module (production_gui_window_taskbar_widget_shells.spl,
imports only builder/render/engine2d entry) renders fine.

## Expected
Module globals must be initialized before first use regardless of the
importing module's import graph. Workaround in place: lean-import module.
