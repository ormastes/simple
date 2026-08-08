# Interpreter HIR-Lowering Flake on `<style>`-Block `background`/`color` During Software Paint

## Summary

Rendering HTML through the pure-Simple layout renderer's software-pixels entry
`simple_web_layout_render_html_software_pixels` (in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`)
fails under the interpreter/JIT with a semantic HIR-lowering error whose message
NAMES THE CSS PROPERTY:

```
semantic: variable `background` not found
# or, for a `color:` block rule:
semantic: variable `color` not found
# standalone `run` surfaces it as:
JIT compilation failed, falling back to interpreter: HIR lowering error:
Unknown variable: background while lowering main
```

It reproduces on clean `main` (verified by reverting the renderer to
`HEAD` — the failure is identical), so it is NOT introduced by the iframe
embedding work; it was hit while writing that feature's CSS-scoping spec.

## Trigger (minimal)

```
<html><head><style>div{background:#ff0000}</style></head><body>
  <div style='height:50px'>hi</div>
</body></html>
```

Rendered via `simple_web_layout_render_html_software_pixels(html, w, h)`.

- Fails for the color-valued **shorthands** `background:` and `color:` in a
  `<style>` BLOCK.
- Does NOT fail for the `background-color:` longhand, nor for `width`, `height`,
  `display`, `border`, `margin`, `padding` block rules.
- Does NOT fail for the same `background:`/`color:` shorthands used INLINE
  (`style='background:#ff0000'`) — only the `<style>`-block path.
- The `simple_web_layout_debug_style_by_id` entry (parse + compute_styles, no
  `layout`/`paint`) does NOT trip it — the full `layout`+`paint` render is
  required.

## Order-dependence (flake)

The failure is order-sensitive across a spec file: the FIRST style-block
full-paint render in a fresh compilation can fail, while an equivalent render
that runs after a benign non-color block render (e.g. `div{width:1px}` with an
`<iframe>` present) succeeds. This points at incomplete cross-function name
resolution during the interpreter's LAZY JIT lowering rather than a genuine
undefined variable in the renderer source (a real undefined would fail
deterministically whenever the owning function compiles). The property name
leaking into the "variable X not found" message suggests the color-shorthand
apply branch is the function that fails to lower.

## Impact / Workaround

The iframe embedding spec's `space=separate`/`space=shared` scenario needs a
parent `<style>` block (only block rules participate in "shared"). To stay green
and honest it measures the shared effect through a `div{height:70px}` block rule
(safe property) against an inline-blue child, preceded by a benign iframe +
`div{width:1px}` warm-up render. See
`test/02_integration/rendering/simple_web_iframe_embedding_spec.spl`.

## Fix direction

Root-cause the interpreter's lazy HIR lowering for the CSS color-shorthand apply
path (grep the renderer for the `background`/`color` shorthand expansion reached
only from the block cascade). Likely the same class as other "variable X not
found while lowering" lazy-JIT resolution gaps. A compiled (non-interpreter)
build should be checked to confirm it is interpreter-only.
