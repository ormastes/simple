# Browser Engine Implementation Guide

The Simple browser engine is a GPU-accelerated HTML/CSS renderer in the canonical engine at `src/lib/gc_async_mut/gpu/browser_engine/`. It targets Chromium-class rendering fidelity through incremental milestone delivery.

**Status**: M13 complete (float layout + CSS quick wins). 132/132 corpus pixel-exact. WPT 104/104 (100%).

## Source Files

| File | Purpose |
|------|---------|
| `src/lib/gc_async_mut/gpu/browser_engine/layout.spl` | Layout engine: block, flex, float, text |
| `src/lib/gc_async_mut/gpu/browser_engine/dom.spl` | DOM tree, style parsing, event dispatch |
| `src/lib/gc_async_mut/gpu/browser_engine/css.spl` | CSS types (StyleProps, CssValue, FloatCode, ClearCode) |
| `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl` | Paint/render pipeline |
| `src/lib/gc_async_mut/gpu/browser_engine/style_block.spl` | CSS cascade, shorthand expansion |
| `src/lib/gc_async_mut/gpu/browser_engine/html_parser.spl` | HTML tokenizer and tree builder |

## Architecture

```
HTML string
  -> html_parser.spl    (tokenize + tree-build -> BeDomNode tree)
  -> dom.spl            (set_style per node, cascade)
  -> layout.spl         (layout_tree -> BeLayoutBox tree)
  -> browser_renderer.spl (paint BeLayoutBox -> SceneCommand list -> GPU)
```

Per ADR-002, this canonical engine is production. The research tree at `examples/11_advanced/browser/` is demoted to labs.

## Layout Engine

### Entry Point

`layout_tree(root, viewport_w, viewport_h) -> BeLayoutBox` creates a root FloatContext and dispatches to `layout_node`.

### Display Dispatch (layout_node)

| Display value | Handler |
|---------------|---------|
| `"none"` | Returns empty BeLayoutBox |
| `"flex"`, `"inline-flex"` | `layout_flex` |
| `"flow-root"` | `layout_block` (BFC auto-detected) |
| text node | `layout_text_node` |
| everything else | `layout_block` |

### Float Layout (M13)

Float layout follows CSS 2.1 section 9.5.1. Key types in `layout.spl`:

- **FloatBox** — positioned float with `x, y, width, height, side` (i32 geometry, side: 1=left 2=right)
- **FloatContext** — tracks `left_floats: [FloatBox]`, `right_floats: [FloatBox]`, `current_y: i32`
- **FloatPos** — return type for placement: `x, y`

Float utility functions:

| Function | Purpose |
|----------|---------|
| `float_available_width_at(y, ctx, total_width)` | Available width minus float intrusions at y |
| `float_left_offset_at(y, ctx)` | Left edge offset from left floats at y |
| `float_clear_y(clear_code, ctx)` | Y after clearing (1=left 2=right 3=both) |
| `float_place(w, h, side, ctx, container_w)` | Place a float, advancing down if no room |
| `float_context_height(ctx)` | Max bottom of all floats (for BFC containment) |

### Block Formatting Context (BFC)

BFC roots get a fresh FloatContext. Detected by:
- `overflow != "visible"` (hidden, auto, scroll)
- `display: flow-root`, `display: flex`, `display: inline-flex`
- Document root (layout_tree creates top-level BFC)

BFC roots expand their height to contain all floats via `float_context_height`.

### Float-Aware Child Loop (layout_block)

For each child in a block container:
1. Check `child_style.clear_code` — if > 0, advance cursor_y past cleared floats
2. Check `child_style.float_code` — if 1 or 2, lay out child, place via `float_place`, register in FloatContext, do NOT advance cursor_y
3. Otherwise (normal flow): narrow container by float intrusions at cursor_y (fast-path skips when no floats exist)

### Text Wrapping Around Floats (layout_text_node)

When FloatContext has active floats, text layout switches to per-line mode:
- Each line queries `float_available_width_at(line_y, ctx, container_width)` for available width
- Characters per line computed from available width and char width
- Fast path: when no floats exist, uses the original ceiling formula (preserves 132-corpus pixel parity)

### Performance Notes

Float context is threaded through all layout functions as a parameter (reference semantics verified). Performance-critical optimizations:
- Direct `i32` field access for `float_code`/`clear_code` (no wrapper object allocation)
- Fast-path guard: `float_available_width_at`/`float_left_offset_at` skipped when float lists are empty
- BFC detection inlined to avoid per-block function call overhead
- Flex children reuse parent FloatContext instead of allocating fresh empty contexts

## BrowserSession JavaScript Boundary

Browser-profile JavaScript `fetch()` only queues a request. `BrowserSession`
resolves the URL against the committed page, enforces scheme/origin and
mixed-content policy, strips page-supplied `Cookie`, and attaches cookies from
the session jar. The JS interpreter does not perform direct file or HTTP I/O.
The shared fetch transport rejects redirects from HTTPS to plaintext before
creating the redirected request.

`document.cookie` receives only origin-visible, non-HttpOnly cookies.
Transport cookies and internal module/fetch state are not installed as
page-visible `window`, `chrome`, or global properties.

## CSS Quick Wins (M13)

| Feature | Status | Location |
|---------|--------|----------|
| `hsl()`/`hsla()` | Already implemented | `dom.spl:parse_hsl_func` |
| `currentColor` | Implemented | `dom.spl` — background-color, border-color, outline-color |
| `display: inline-flex` | Implemented | `layout.spl:layout_node` dispatches to `layout_flex` |
| `display: flow-root` | Implemented | `layout.spl:layout_node` dispatches to `layout_block` (BFC auto-detected) |
| `list-style: none` | Already works | Engine renders no list markers |
| `flex-flow` shorthand | Already implemented | `style_block.spl` expands to flex-direction + flex-wrap |
| `calc()` arithmetic | Already implemented | `css.spl:css_resolve_calc_px` handles +,-,*,/ for px |

## Testing

```bash
# 132-page corpus regression gate (must remain pixel-exact)
bin/simple test test/03_system/wm_compare/famous_site_corpus_spec.spl

# Same, cache-busted (use after layout changes)
bin/simple test test/03_system/wm_compare/famous_site_corpus_spec.spl --clean

# Float layout unit tests
bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/float_layout_spec.spl

# CSS routing tests
bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_ext_routing_spec.spl

# All browser engine tests
bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/

# Layout box content contract (system tier)
bin/simple test test/03_system/browser_engine/layout_box_content_contract_spec.spl

# Enable layout debug output
SIMPLE_DEBUG_LAYOUT=1 bin/simple run <script.spl>
```

### Layout box content contract

`BeLayoutBox` stores the **border box** (`x`/`y`/`width`/`height`) plus the box
model, and derives the content rectangle on every call:

    content_x      == x + padding_left + border_width
    content_y      == y + padding_top  + border_width
    content_width  == width  - padding_left - padding_right  - border_width * 2
    content_height == height - padding_top  - padding_bottom - border_width * 2

Two things follow, and both have already caused dead code:

- `content_x` / `content_y` / `content_width` / `content_height` are **methods,
  not fields**. Reading them as fields does not compile.
- A box refers to its element by the integer `node_id` field (`-1` for
  anonymous boxes). There is no `node` field holding a `BeDomNode`; resolving a
  node from a box needs a `node_id` lookup that no current pipeline provides.

The deleted `_paint_box` helper got both wrong and could never execute — see
`doc/08_tracking/bug/layout_paint_paint_box_dead_code_wrong_belayoutbox_shape_2026-08-15.md`.
The contract is now stated executably by
`test/03_system/browser_engine/layout_box_content_contract_spec.spl` (plan:
`doc/03_plan/sys_test/browser_engine_layout_box_content_contract.md`), whose
third scenario mutates padding after construction specifically to prove the
content rectangle is derived per call rather than stored.

The engine does **not** clamp an over-constrained box: padding and border wider
than the box yield a negative `content_width()`, which callers must handle.

## Production Web Boundary Checks

Browser-engine changes that affect Simple Web production behavior must preserve
both the renderer parity gate and the web endpoint hardening gate:

```bash
sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs
bin/simple test test/03_system/gui/simple_web_browser_production_hardening_spec.spl --mode=interpreter --clean --timeout 360
```

The endpoint gate covers the selected Feature Option C / NFR Option C
production web boundary: allowed-origin login only, bounded login requests,
sensitive API denial without an origin-bound bearer token, canonical `/ui/ws`
bearer authorization, and legacy `/ws` hiding. Browser clients should use
WebSocket subprotocol bearer auth; query-string bearer fallback is deprecated
and non-authorizing, including when `SIMPLE_UI_WEB_ALLOW_QUERY_TOKEN=1` is
present.

Hosted browser frames are admitted by `HostCompositor` per window. Admission
requires the current content-box dimensions, Simple Web provenance, and a valid
pixel checksum; four slots share a 16,777,216-pixel retention budget. Resize
empties the affected slot and window destruction removes only that slot. Both
primary and secondary hosted browser windows use it. Secondary windows own
bounded, window-keyed renderer/raster entries; minimized entries still poll
cleanup and deadlines without scheduling animation work. Missing, failed, or
over-capacity renderer admission stays blank rather than falling back to parent
HTML/JavaScript execution. Fresh pure-Simple live evidence is still required
before describing the multi-window path as production-proven.

BrowserSession retains at most 128 distinct warnings (4096 characters each).
The sandbox worker builds its 4096-character frame diagnostic incrementally;
it never joins the full warning history on animation frames.
Failed child close retries once per second, and successful close releases the
broker decoder/cache/history state retained by its failure tombstone while
preserving learned HSTS for persistence.

On Linux, renderer READY is admissible only after the executable preinit hook
has activated the stage-one Landlock/seccomp marker. Calling the stage-two
sandbox entry without that marker fails closed before applying worker limits;
`test/01_unit/runtime/run_process_piped_write_test.shs` covers both paths:

```bash
sh test/01_unit/runtime/run_process_piped_write_test.shs
```

Its PASS receipt proves only the current runtime
`rt_browser_renderer_spawn_sandboxed` preinit plus
`rt_browser_renderer_sandbox_enter` second-stage path: environment/cwd/
inherited-FD sanitization and Landlock/seccomp/rlimit containment/limits. It
does not admit a hosted renderer artifact, prove broker/CSP enforcement or
Electron containment, or promote a production SANDBOX row.

### Post-load and transport invariants

- Dynamic JavaScript/Simple Script background URLs re-enter the existing
  `_start_image_source` broker path; never fetch or decode them in the renderer.
- Do not rebuild the JS timer queue while draining. Select within the bounded
  list, reschedule intervals in place, and remove completed/canceled slots.
- A partially written renderer command is atomic. Record `stop_after_write`,
  finish it, then cancel state and send Stop; drain complete frames already in
  the worker decoder before another read.
- Keep bracketed IPv6 in URLs and origins. Pass only the validated bare literal
  returned by `_browser_transport_host` to socket/TLS.
- Final Linux renderer seccomp denies `get_robust_list` with the existing
  cross-process inspection syscalls.

Host C containment/TLS checks are supporting evidence. Until the pure-Simple
target runs the affected scenarios, do not claim a browser runtime PASS or
substitute bootstrap/Rust-seed execution.

Run the local OpenSSL client ABI gate with:

```bash
sh scripts/check/check-runtime-https-openssl.shs
```

It covers `rt_tls_client_*` address+SNI trusted, mismatch, untrusted, stall,
reset, and trickle cases. It does not exercise hosted `rt_browser_http_job` or
a live `BrowserSession`, and cannot promote a TLS production row.

### Event-routing proof launch

Run the event proof only with a fresh Aetheric admission receipt and matching
Simple composition receipt:

```bash
AETHERIC_HOST_WEB_GUI_PROOF=/absolute/path/aetheric-host-web-gui.env \
SIMPLE_WEB_FONT_RUN_ID=<fresh-run-id> \
SIMPLE_WEB_FONT_COMPOSITION_RECEIPT=/absolute/path/receipt.env \
sh scripts/check/check-wm-browser-event-routing-evidence.shs
```

The production command keeps Electron's Chromium sandbox and GPU defaults
enabled. `ELECTRON_DISABLE_SANDBOX` and
`WM_BROWSER_EVENT_ROUTING_DIAGNOSTIC_FLAGS` are diagnostic-only: the wrapper
records blocked/unavailable and cannot emit PASS. A successful receipt
includes the admitted Aetheric artifact SHA-256/readback identity and the
Simple composition artifact SHA-256, joining event/animation evidence to its
pixels.

The wrapper does not infer sandbox or GPU state from that command. Its renderer
preload exposes Electron's `process.sandboxed` value, while the main process
records `app.getGPUFeatureStatus()`. Production validation requires sandbox
`true` plus `enabled` GPU compositing and WebGL. Software, unavailable, missing,
or altered values fail closed.

Pinned WPT/Test262 identity and the visible unsupported ledger live under
`test/fixtures/browser/conformance/`. Validate their non-PASS metadata with:

```bash
sh scripts/check/check-simple-web-browser-conformance-contract.shs
```

This check neither downloads suites nor claims conformance.

### Current frame and chrome invariants

- CSS background Draw IR includes canonical clip-shape bounds and per-axis radii.
  Engine2D masks while sampling and caps aggregate background pixel work at one
  framebuffer per composition.
- `opacity: 0` removes the whole subtree from layout/paint. Do not emulate
  fractional opacity per primitive; add it only with bounded group compositing.
- Bookmark mutations publish one snapshot/revision to primary, secondary, and
  newly opened browser renderers.
- Escape restores the committed URL, or the window's startup address before the
  first commit. Keep this identical in primary and registry lanes.
- Both HTTP job owners use `hosted_browser_transport_host`; URLs retain brackets
  while socket/TLS receives a validated bare IPv6 literal.
- Coalesce adjacent deferred resizes to the newest size. Serialize the document
  once per animation frame and reuse it for animation reconciliation and render.

## Milestone History

| Milestone | Gate | Status |
|-----------|------|--------|
| M1-M12 | 132/132 corpus, Acid2, 30/30 design effects | Complete |
| M13 | Float layout, CSS quick wins, 132-corpus regression | Complete (AC-7 WPT waived) |
| M14+ | See `doc/03_plan/ui/web_browser/simple_browser_chrome_class_roadmap.md` | Planned |

## References

- [Chrome-class roadmap M13-M24](../../03_plan/ui/web_browser/simple_browser_chrome_class_roadmap.md)
- [ADR-002: Canonical Browser Engine](../../04_architecture/adr/ADR-002-canonical-browser-engine.md)
- [CSS 2.1 Float Specification](https://www.w3.org/TR/CSS2/visuren.html#floats)
