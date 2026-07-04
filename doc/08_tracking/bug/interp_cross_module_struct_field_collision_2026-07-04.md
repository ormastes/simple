# Interpreter: cross-module struct field-resolution collision with DIFFERENT struct names (Style vs CellStyle)

**Date:** 2026-07-04
**Severity:** high — blocks CARD 16 office GUI; broader instance of the
ledgered same-name struct collision
**Status:** open — deterministic repro

## Symptom

Once BOTH `src/app/office/sheets/cell.spl` (`CellStyle`: bold, italic, align,
format) and the browser engine's `Style` struct (bold, italic, …, display,
…) are loaded in one interpreter process, constructing/copying ANY `Style`
value fails:

```
error: semantic: class `CellStyle` has no field named `display`
```

~4s deterministic failure, unconditional on CSS content (reproduced with
every `display:` property removed). Not present when `Style` is exercised
without sheets code loaded (all browser-engine specs pass).

## Why it matters beyond the GUI

The previously ledgered bug required the SAME struct name in two modules.
Here the names DIFFER (`Style` vs `CellStyle`) — the interpreter's runtime
struct-literal/copy resolution appears to match by field-name-set overlap
(bold/italic shared), not declared type. Any two structs sharing a field
subset across modules are at risk when co-loaded.

## Repro

`office counter --gui` fallback path in `src/app/office/gui.spl`
(`office_gui_minimal_css()` knob) — bypasses render_frame, calls
`render_html_tree()` + `simple_web_engine2d_render_html_pixels()` directly
with ~1KB CSS; fails fast with the error above. Full analysis in
doc/08_tracking/bug/browser_engine_css_size_quadratic_pixel_render_2026-07-04.md
(Round 3 lane section).

## Related open item (same doc)

Separate unexplained gap: the identical render call is fast under
`bin/simple test <spec>` but hangs 60s+ under
`bin/simple run src/app/office/mod.spl` (full office module graph as entry) —
suspect symbol-count-scaled dispatch overhead or JIT-fallback difference.

## Next step

Find the interpreter's struct-literal/copy-update resolution (likely
matching by field-name set) in src/app/interpreter/ or
src/compiler/70.backend/backend/interpreter*.spl; resolution must key on the
declared/inferred TYPE, not field names. Cross-ref:
[[interp_dict_in_struct_copy_corruption_2026-07-03]],
[[interp_array_param_indexing_2026-07-03]].
