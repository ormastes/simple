<!-- codex-research -->
# Showcase apps — local research

The repository has three partial showcase lanes, but no shared catalog or complete surface matrix.

- 2D: `examples/06_io/ui/engine2d_shapes_gui.spl` is standalone CPU raster code and does not exercise the canonical Engine2D backend/readback contract.
- GUI: `examples/06_io/ui/widget_showcase_gui.spl` has real standalone input and a filesystem-frame host-WM client. `examples/06_io/ui/wm_widget_showcase_gui.spl` is the only host-WM showcase wrapper.
- Web: `examples/06_io/ui/web_render_file_gui.spl` renders files, while `src/app/ui.browser/app.spl` owns the interactive BrowserApp. Its shared-WM branch currently starts a compositor without loading the requested file.
- SimpleOS: `/sys/apps/browser_demo` is a static widget/text demo, and the launcher/catalog has no 2D or GUI showcase identities.

Known false-positive paths include background-only, white, and striped browser renderers; synthetic widget events; source-string WM assertions; and GUI-unavailable paths that return success. These cannot prove a showcase surface.

The safe architecture is one catalog, three canonical app IDs, and adapters for standalone, host WM, and SimpleOS WM. Each adapter must retain actual pixel/event evidence and report unsupported features explicitly.
