# Web file renderer nil-receiver crash

## Status

Open. Blocks `web_standards_showcase` standalone readiness.

## Reproduction

```text
env -u SIMPLE_GUI SIMPLE_TIMEOUT_SECONDS=60 bin/simple run examples/06_io/ui/web_render_file_gui.spl --mode=interpreter
runtime error: field access on nil receiver
exit=132
```

The control run with `examples/06_io/ui/sample_web_renderer_sanity.html` fails identically, so this is not specific to an advanced element in the new standards page. It occurs before the renderer's first provenance line.

## Impact and ownership

The active worktree already contains concurrent changes in `simple_web_html_layout_renderer.spl` and the browser/compositor lane. Those files were not modified by this showcase lane. The crash must be diagnosed against the settled renderer change before enabling catalog readiness.

## Acceptance

- Both the legacy sanity page and `browser_common_elements_showcase.html` render without a nil receiver.
- Unsupported elements produce explicit diagnostics rather than blank success or a crash.
- The focused showcase test records visible content, backend provenance, dimensions, nonblank pixels, and real interaction state.
