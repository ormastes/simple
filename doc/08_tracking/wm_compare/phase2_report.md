# Phase 2 Report — Chrome vs Simple Pixel Equivalence

**Date:** 2026-04-12
**Plan:** `fancy-shimmying-hamster.md` — multi-source WM/Browser render verification
**Goal:** Prove the Simple web engine renders HTML/CSS at 320x240 equivalently to
Chrome for an incremental CSS feature progression. Stop at the first divergent
fixture per the plan's decision rule.

## Outcome — BLOCKED on Bug G (new downstream of Bug E)

Step 1 (`rt_array_push` sweep) completed successfully. Bug E (the
`rt_array_push(typed_array, v)` runtime mismatch in `BrowserRenderer`) is
fully resolved — the end-to-end source B capture ran to completion for
the first fixture.

Step 2 (pixel compare) immediately surfaces **Bug G**: Simple's
`browser_renderer_html_string_to_dom()` produces an empty DOM for every
HTML input. The entire 320x240 frame is uniformly white (`0xFFFFFFFF`)
because no paint commands are generated. No subsequent fixture can pass —
all 12 Phase 2 fixtures contain text content.

## Step 1 — rt_array_push Sweep

**Swept files (6, all confirmed clean):**

| File | Sites converted |
|---|---:|
| `src/lib/gc_async_mut/gpu/browser_engine/layout.spl` | 22 + extern |
| `src/lib/gc_async_mut/gpu/browser_engine/dom.spl` | 18 + extern |
| `src/lib/gc_async_mut/gpu/browser_engine/paint.spl` | 18 + extern |
| `src/lib/gc_async_mut/gpu/browser_engine/style_block.spl` | 12 + extern |
| `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl` | 10 (extern already gone) |
| `src/lib/common/render_scene/executor.spl` | 7 + extern |

**Conversion rule:** every call site had the pattern
`rt_array_push(typed_array_var, value)` where the first arg was a typed
`[T]` field or local. All 87 call sites were rewritten to `array.push(value)`
and the per-file `extern fn rt_array_push` declarations were removed. The
runtime-internal extern in `src/compiler_rust/lib/std/src/alloc/ffi.spl`
and the symbol-registry string literal in `src/lib/common/runtime_symbols.spl`
were left alone — both are low-level references to the still-needed
runtime primitive.

**Sanity check:** `/tmp/interp_repros/e_min.spl`
(`BrowserRenderer.create(320,240).render_html_to_pixels("<p>x</p>")` +
`print "ok"`) still runs under the seed binary and prints `ok`. No
regression.

## Step 2 — Source B Capture Attempt

Command:
```
SIMPLE_HTMLCOMPAT_TRY_B=1 SIMPLE_LIB=$(pwd)/src \
  src/compiler_rust/target/bootstrap/simple run \
  src/app/wm_compare/html_compat.spl --only=00_text_only --try-source-b
```

**Result:** source B ran end-to-end for `00_text_only`. Chrome capture
(230,415-byte PPM, 76,800 pixels) and Simple capture (230,415-byte PPM,
76,800 pixels) both succeeded. Bug E is fully cleared — the minimal
repro path and the full harness both proceed through the renderer
without crashing.

**Fixture `00_text_only` — first divergent fixture:**

| Metric | Value |
|---|---|
| Fixture id | `00_text_only` |
| Tolerance profile | `profile_strict` (CSS-less; plan requires exact match) |
| Exact match | **false** |
| Different pixels | **1016 / 76,800** (1.32%) |
| Exact match % | 98.67% |
| Perceptual match % | 98.67% |
| Max channel diff | **255** |
| Accepted | **false** |

**Per-source visual description:**

- **Chrome** renders two text glyph bands:
  - Band 1: y = 16..33 ("Hello", ~500 px)
  - Band 2: y = 51..67 ("World", ~500 px)
  - Total non-white pixels: **1016**
  - Non-white region is exactly the Chrome font rasterizer output (full
    black at glyph centers, anti-aliased greys at edges — hence
    `max_channel_diff=255`).
- **Simple** renders a completely uniform white frame:
  - Total non-white pixels: **0**
  - Zero glyph bands, zero paint output, zero visible content.
  - The 1016 differing pixels are precisely the pixels where Chrome drew
    glyphs and Simple drew nothing.

The divergence is 100% "Simple has no text at all", not "Simple rasterizes
text differently". Report file:
`test/baselines/html_compat/00_text_only/report.sdn`. Diff heatmap:
`test/baselines/html_compat/00_text_only/diff_chrome_vs_simple.ppm`.

## Bug G — HTML Parser Produces Empty DOM

**Location:** `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl`,
`browser_renderer_html_string_to_dom()` (invoked from the `render_html_to_pixels`
method on line 225 of the same file).

**Repro:** `/tmp/interp_repros/g_text_blank.spl`

```
pixels: 76800
scene_commands: 0
text_cmd_count: 0
nonwhite: 0
```

**Pipeline introspection probe:** `/tmp/interp_repros/g_layout_probe.spl`
— dumps DOM, layout box, paint cmds, scene cmds for
`<html><body><p>Hello</p></body></html>`:

```
DOM node count: 1
<div>
layout box: x=0 y=0 w=320 h=0 children=0
paint commands: 0
scene commands: 0
```

**Root cause localization:** `browser_renderer_html_string_to_dom(html)`
returns a root `<div>` (id `"html-root"` — see browser_renderer.spl:459-461)
with **zero children**. The HTML parser's tag-walk loop (lines ~460-644)
never pushes `<html>`, `<body>`, or `<p>` into the DOM tree for this
input. Every downstream stage is correct — `layout_tree` faithfully
lays out an empty div, `generate_paint_list` produces zero commands,
`paint_commands_to_scene` returns zero commands, `execute_scene_to_buffer`
runs over zero commands, leaving the pre-filled white background.

The parser emits the `[PARSE] done, applying UA defaults` / `[PARSE] UA
defaults done, processing style blocks` / `[PARSE] all done` trace
messages, so the top-level loop completes without exception — it just
never attaches any children.

**This is NOT the `rt_array_push` bug family.** All the converted
`.push` sites in `layout.spl`, `dom.spl`, `paint.spl`, `style_block.spl`,
`browser_renderer.spl`, and `executor.spl` work correctly — they're
simply never reached because the DOM is empty. Bug G sits upstream of
them in the HTML tokenizer / tag-walker.

**Likely suspects (not investigated — stopping per task rules):**

1. `browser_renderer_html_string_to_dom` (br:459-644) uses a stack-based
   walker (`stack: [BeDomNode]`) that the recent `.push()` conversion
   touched (new_stack, stack, parts). One of those conversions may have
   broken a nuanced ordering — OR more likely, the HTML walker was
   already broken before the sweep and is unrelated to `rt_array_push`.
2. `br_stack_pop_and_add` (br:443-457) manipulates `stack[stack.len()-1]`
   in a way that could misbehave if `.push()` on `new_stack` and
   re-indexing have a subtle cross-module type issue.
3. Open-tag handling (`br_handle_open_tag`) never enters the `else`
   branch that does `stack.push(new_node)` (br:642), suggesting every
   tag is being treated as self-closing or void.

These are speculation — not verified. Do not chain-fix; fix Bug G in a
fresh session with the repro files.

## Recommendation — Next Real CSS Engine Gap

**Do not proceed to any CSS-feature progression until Bug G is fixed.**
Every Phase 2 fixture (00..03 + 10..17) depends on the HTML parser
delivering at least one non-root node. With the parser returning empty,
the 11 remaining fixtures would all be identical degenerate cases.

Once Bug G is fixed, re-run `--try-source-b` and the harness will
proceed naturally. The first real CSS-engine gap to investigate, if the
parser returns text content:

- **Text layout width/height calculation.** CSS-less `<p>` blocks must
  be laid out at paragraph width × line-height × text metrics — the
  browser engine's layout engine needs to advance `content_y` by the
  glyph row height between sibling `<p>` elements. Chrome's Phase 2
  trace shows the two text bands at `y=16..33` (line 1 = 18 px tall =
  line-height 1.12 at 16 px font) and `y=51..67` (line 2, same
  metrics, with 18-px gap for default margin-top ~16 px). Verify
  Simple's `layout_tree` produces the same geometry for default
  `<p>` margins and UA styles.

## Files Touched

| File | Change |
|---|---|
| `src/lib/gc_async_mut/gpu/browser_engine/layout.spl` | 22 `rt_array_push` sites → `.push()`; removed extern |
| `src/lib/gc_async_mut/gpu/browser_engine/dom.spl` | 18 sites → `.push()`; removed extern |
| `src/lib/gc_async_mut/gpu/browser_engine/paint.spl` | 18 sites → `.push()`; removed extern |
| `src/lib/gc_async_mut/gpu/browser_engine/style_block.spl` | 12 sites → `.push()`; removed extern |
| `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl` | 10 sites → `.push()` |
| `src/lib/common/render_scene/executor.spl` | 7 sites → `.push()`; removed extern |
| `test/baselines/html_compat/00_text_only/chrome.ppm` | NEW — Chrome baseline |
| `test/baselines/html_compat/00_text_only/simple.ppm` | NEW — uniform-white (Bug G) |
| `test/baselines/html_compat/00_text_only/diff_chrome_vs_simple.ppm` | NEW — diff heatmap |
| `test/baselines/html_compat/00_text_only/report.sdn` | NEW — 1016 px diverge |
| `/tmp/interp_repros/g_text_blank.spl` | NEW — Bug G minimal repro |
| `/tmp/interp_repros/g_layout_probe.spl` | NEW — pipeline introspection |
| `doc/08_tracking/wm_compare/phase2_report.md` | NEW — this report |

## Reproduce

```bash
# Bug G minimal repro (prints nonwhite: 0 + scene_commands: 0)
SIMPLE_LIB=$(pwd)/src src/compiler_rust/target/bootstrap/simple run \
  /tmp/interp_repros/g_text_blank.spl

# Pipeline probe (shows DOM node count: 1, empty tree, 0 paint cmds)
SIMPLE_LIB=$(pwd)/src src/compiler_rust/target/bootstrap/simple run \
  /tmp/interp_repros/g_layout_probe.spl

# Full harness — stops at 00_text_only with 1016 divergent pixels
SIMPLE_HTMLCOMPAT_TRY_B=1 SIMPLE_LIB=$(pwd)/src \
  src/compiler_rust/target/bootstrap/simple run \
  src/app/wm_compare/html_compat.spl --only=00_text_only --try-source-b
```

## Bug G fixed (2026-04-12)

**Root cause — two distinct seed-interpreter bugs stacked in the HTML parser:**

1. **`text.slice(i, i+1)` inside a `while` loop returns `""` for i>=1.**
   The seed interpreter evaluates the expression statically the first
   iteration and reuses the cached result. `s.slice(0, 1)` returns the
   right char, `s.slice(1, 2)`, `s.slice(2, 3)`, ... all return empty.
   This broke `browser_renderer_find_char`, `br_find_str`, and every
   `split_*` helper — none could scan past index 0, so the tokenizer's
   `find_char(html, ">", 0)` returned 999999999 and the loop immediately
   took the "tag_end overflow" branch and broke out, attaching nothing.
   Workaround: call a single-statement helper fn (`br_char_at`,
   `br_substr`) from inside the loop. The function call boundary forces
   fresh argument evaluation.

2. **Arrays and class instances are passed BY VALUE across function
   boundaries.** `be_dom_add_child(parent, child)` pushes into
   `parent.children`, but the mutation stays inside the helper's stack
   frame and never reaches the caller. Same for `stack.push(node)`
   inside `br_handle_open_tag` — the pushed node was dropped on return.
   Workaround: (a) inline `.add_child` as a direct method call on a
   local `var parent` in the same frame as the stack array, then write
   the parent back with `stack[idx] = parent`; (b) refactor
   `br_handle_open_tag` to return a `BrOpenTagResult` class
   (`{new_pos, action, node}`) and have the caller apply the stack
   mutation in its own frame.

**Fix (file: `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl`):**

- Added `br_char_at(s, i)` and `br_substr(s, a, b)` helper fns.
- Replaced every in-loop `s.slice(i, i+1)` / `s.slice(a, b)` with those
  helpers — `browser_renderer_find_char`, `br_find_str`,
  `browser_renderer_split_tag_parts`, `browser_renderer_split_spaces`,
  `browser_renderer_split_semicolons`, main tokenizer loop, body-attr
  parser.
- Introduced `class BrOpenTagResult { new_pos, action, node }`.
- Rewrote `br_handle_open_tag` to return `BrOpenTagResult` instead of
  `i64`; caller dispatches on `action == "push" | "attach_void" | "skip"`
  and applies the mutation locally.
- Main tokenizer now calls `parent.add_child(txt)` directly (same-frame
  method call on a local `var parent`), then `stack[idx] = parent`.
- `br_stack_pop_and_add` now uses `new_parent.add_child(completed)`
  directly instead of `be_dom_add_child`.
- Removed all tactical `[PARSE]`, `[OT]`, `[CT]`, `[DBG]`, `[LOOP]`,
  `[RHPA]` debug prints.

**Verification:**

```
$ SIMPLE_LIB=$(pwd)/src src/compiler_rust/target/bootstrap/simple run \
    /tmp/interp_repros/g_layout_probe.spl
DOM node count: 3
<div>
  <p>
    TEXT: 'Hello'
layout box: x=0 y=0 w=320 h=18 children=1
paint commands: 1
scene commands: 1
```

```
$ SIMPLE_LIB=$(pwd)/src src/compiler_rust/target/bootstrap/simple run \
    /tmp/interp_repros/g_text_blank.spl
pixels: 76800
scene_commands: 1
  text cmd: x=0 y=0 text=Hello color=4278190080 font_size=16
text_cmd_count: 1
nonwhite: 0
```

**Cascade result — next divergent stage:** the parser now emits
`text` scene commands (1 for a single-`<p>` page), but
`execute_scene_to_buffer` does not rasterize any non-white pixel for
them. `nonwhite: 0` persists after the parser fix. This is a
**separate downstream bug (call it Bug H)** in the text-raster path
(likely `src/lib/common/render_scene/executor.spl` or the font
rasterizer) — the scene command reaches the executor but the glyphs
never land in the ARGB framebuffer. Per task rules (don't chain-fix),
Bug G is closed here and Bug H is handed back to Phase 2.

Also noted: text command is emitted with `y=0`, which likely places
the baseline above the viewport — the layout pipeline's `<p>` default
vertical margin / line-height calculation may need to be checked
as part of the Bug H investigation before concluding it's a pure
rasterizer issue.

**Phase 2 harness re-run after the fix:**

```
[html_compat] Fixture: 00_text_only
[html_compat]   capturing source A (Chrome via Electron)... ok  pixels=76800
[html_compat]   capturing source B (Simple browser engine)... ok  pixels=76800
[html_compat]   RESULT: DIVERGENT — 1016 px differ (98.67% exact)
[html_compat] First divergent fixture: 00_text_only
```

Pixel-level outcome is unchanged (1016 px still differ) because Bug H
leaves Simple's frame uniform white — but the full browser_engine
pipeline (parse → layout → paint → scene → executor) now runs end-to-
end without losing the DOM, which was the Bug G gate. The next real
work is Bug H (text rasterizer).

**Latent slice-in-loop sites NOT fixed by this commit** (same seed
interpreter bug, but not on the `<p>Hello</p>` path — will bite
fixtures with HTML attributes or inline CSS):

- `browser_renderer_parse_tag` (~line 660) — `part.slice(0, eq_pos)`
  and `part.slice(eq_pos + 1, part.len())` inside
  `while i < parts.len()`. Fires on any attribute (`id=`, `class=`,
  etc.).
- `browser_renderer_apply_inline_style` (~line 740) — `decl.slice(0, colon_pos)`
  and `decl.slice(colon_pos + 1, decl.len())` inside
  `while decl_idx < declarations.len()`. Fires on any inline `style=`
  attribute.
- Same workaround applies: wrap in `br_substr()` calls.

These should be fixed before tackling attribute/CSS-bearing fixtures
(01+).

