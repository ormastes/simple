# DrawIR render path crashes with `trim on nil` on ANY element document — `<div>x</div>` is enough

- **ID:** web_draw_ir_path_trim_on_nil_any_element_2026-07-26
- **Date:** 2026-07-26
- **Area:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
  (`_simple_web_layout_render_html_draw_ir_result`) →
  `..._paint_layout.spl` (`_html_draw_ir_commands`)
- **Severity:** high — DrawIR is the path the SimpleOS WM compositor and the web
  showcase cells render through.
- **Status:** **FIXED 2026-07-26.** Root cause was none of the three candidate
  sites below — see the resolution section at the end. The underlying
  interpreter defect is filed separately as
  `interp_env_get_name_collision_nil_root_2026-07-26.md` and remains OPEN.

## Minimal repro

```
use std.gc_async_mut.gpu.browser_engine.simple_web_html_layout_renderer.{simple_web_layout_render_html_draw_ir_result}
fn main():
    val r = simple_web_layout_render_html_draw_ir_result("<div>x</div>", 24, 16)
    print "OK"
```

```
error: semantic: method `trim` not found on type `nil` (receiver value: nil)
rc=1
```

`<div style='width:24px'>x</div>` and `<div style='width:24px;height:16px'>x</div>`
fail identically. A document with **no elements at all** (`<!-- only a comment -->`)
succeeds — so the crash needs at least one element node.

## Why it was not caught earlier

The existing fixture
`test/03_system/compiler/fixtures/web_material_fallback_css_state_probe.spl`
passes. Every document in it carries `data-wm-theme-fallback=...`,
`data-wm-theme-bg=...`, `data-wm-theme-fg=...`. Those attributes are exactly
what the suspect `.trim()` sites read. The fixture therefore exercises only the
attribute-**present** branch, and an ordinary `<div>` — the overwhelmingly
common case — is untested. **The fixture should gain a bare-element case.**

## Bisection

| variant | result |
|---|---|
| software path, `<div style=...>x</div>` | **OK** (`kind=none`) |
| DrawIR path, `<div>x</div>` | **crash** |
| DrawIR path, comment-only document | OK |

Software and DrawIR share everything up to `layout(...)`. The delta is
`simple_web_html_layout_renderer.spl:219-230`: `_html_draw_ir_commands`,
`_web_canvas_background`, the `draw_ir_*` constructors, and
`_simple_web_realized_material_fallback`.

**Not caused by the 2026-07-26 browser-engine change.** Reverting both
`..._core.spl` and `..._foundation.spl` to `8469c335ed8` (before the
portable-text change landed) reproduces the crash identically.

**`attr_value` is cleared.** It is declared `-> text` and returns `""` on every
not-found path. Probed directly:

```
attr_value("div", "data-wm-theme-fallback")  ->  "" (not nil)
attr_value("div", "type")                    ->  "" (not nil)
attr_value("div class='x'", "class")         ->  "x"
```

So the nil is introduced somewhere else on the receiver chain.

## Candidate sites

All three are `attr_value(...).trim()` in
`simple_web_html_layout_renderer_paint_layout.spl`:

```
118:  val input_type   = attr_value(nd.attrs_raw,   "type").trim().lower()
549:  val wm_fallback  = attr_value(node.attrs_raw, "data-wm-theme-fallback").trim().lower()
942:  val shared       = attr_value(nd.attrs_raw,   "space").trim().lower() == "shared"
```

Since `attr_value` itself does not return nil for a missing attribute, the next
hypothesis to test is that **`nd.attrs_raw` is nil** for some node kind (e.g. a
`#text` node built through a path that leaves the field unset), and that the
seed interpreter propagates that nil out of `attr_value` rather than faulting
inside it. Note `mk_node()` initialises `attrs_raw: ""`, so a nil there would
itself be a defect — plausibly the struct-init/field-decode class already
recorded in session memory.

## Reproduce

```bash
bin/simple run probes/dg_draw_ir_min.spl        # rc=1
```

## Resolution (2026-07-26)

The three candidate sites above were all innocent — `attrs_raw` is initialized
on every `HNode` constructor path. Receipt-probe descent pinned the crash to
`font_registry.spl` `_font_asset_normalized_root`, reached only on the DrawIR
path because it passes `vector_fonts=true` into `compute_styles`, which resolves
font metrics for every `#text` node (the software path passes `false` — that is
the real software/DrawIR delta, not the DrawIR command builders).

The nil came from `env_get("SIMPLE_ASSET_ROOT")` returning **nil** instead of
`""` for the unset variable: the interpreter resolves the module's explicit
`use std.io_runtime.{env_get}` to a same-named Option-returning `env_get` from
another module in the graph
(`interp_env_get_name_collision_nil_root_2026-07-26.md`). Environments that
export `SIMPLE_ASSET_ROOT` never crash, which is why the fixture suite stayed
green.

**Fix:** nil-guard in `_font_asset_normalized_root` (nil root ⇒ unset ⇒ `""`),
the single chokepoint all `SIMPLE_ASSET_ROOT` reads funnel through. Verified:
`probes/dg_draw_ir_min.spl` now prints `DRAW_IR_MIN_OK batches=1`;
`probes/font_load_perf_probe.spl` unchanged (`FONT_PROBE_PASS`, ~1 s).

## Related

- `doc/08_tracking/bug/seed_parser_no_return_expression_kills_jit_2026-07-26.md`
  — same run surfaced this; both are deployed-seed defects on the web path
- `doc/08_tracking/bug/simpleos_wm_content_provenance_material_fallback_none_2026-07-25.md`
  — the guest-side symptom this may sit underneath
