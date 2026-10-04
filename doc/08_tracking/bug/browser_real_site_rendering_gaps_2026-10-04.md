# Simple Browser: real-site fetch fixed, rendering gaps remain (2026-10-04)

Status: OPEN (fetch path FIXED in branch `work/browser-tls-status-trace`;
rendering gaps below are still open)

Host: macOS arm64. Binary: Rust seed rebuilt from this branch
(`build/seed_target/release/simple`, `cargo build --release --bin simple`).
Launch: `simple run src/app/browser/main.spl https://<site>`; pixels via
`browser_engine_pixels_at(url, 800, 600)` + `encode_argb_to_png` (scratch
script, not committed).

## Fixed in this branch (root causes)

1. **Every https fetch failed "h1: incomplete TLS write"** — b36a30986ff made
   `TlsConnection.write_text_timeout/read_text_timeout/close` return `Result`,
   but `h1_client.spl` kept comparing the `Result` to a byte count
   (`h1_write_complete(written, len)` was always false) and called `.len()` on
   the read `Result`. `ws_handshake.spl` had the same stale shape.
2. **Seed interpreter had no TLS read extern** — `4edef8fab8e` swapped the
   `rt_tls_client_read_checked`/`rt_tls_client_read_timeout_checked`
   registrations back to the plain reads, and `0891120f3ea` then deleted the
   plain ones, leaving `semantic: unknown extern function:
   rt_tls_client_read_timeout_checked`. Re-registered in
   `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`.
3. **www.google.com: "TLS read failed or timed out"** — Google closes TCP
   without a TLS close_notify after a `Connection: close` response. A read
   error / failed close after body bytes is now accepted ONLY when the
   response is self-delimited (Content-Length or chunked, both strictly
   validated by the parser); a close-delimited body is still refused
   (truncation-attack guard). Certificate verification is untouched.
4. **"Status: loaded" printed after a failed fetch**; exit code was 0.
5. **`hosted_browser_network_error` / `hosted_browser_canonical_navigation_url`
   missing** — `bb3f6ab8ab2` (release transplant) rewound
   `hosted_browser_renderer_policy.spl`; restored from `bb3f6ab8ab2^`.
6. **`draw_ir_command_has_unsupported_v4_state` not found** — forward-port
   `d9fcfc6f01e` added a call to a release-only v4 Draw IR helper whose
   definition (and the v4 command fields) never reached main; every engine
   render failed. Call removed in `draw_ir_adv.spl` (main has no v4 state).
   Still broken, not on the browser path: `src/lib/skia/backend/
   upstream_ganesh_vulkan/provider.spl:5-8` imports v4 symbols main lacks.
7. `[draw-ir-font-trace]` gate used `env_get(..) != nil` (env_get returns ""),
   so it printed per glyph; `[web-style-producer]` CSS-stage receipts printed
   unconditionally. Now `SIMPLE_TRACE_FONT_STYLE=1` / `SIMPLE_WEB_STYLE_TRACE=1`.
8. CSS `light-dark(a,b)` decoded as garbage (yellow); `color-scheme: light
   dark` forced dark text on a light background.
9. ws handshake accepted any status line containing "101".

Specs: `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_real_site_compat_spec.spl`,
`test/02_integration/app/browser_cli_log_modes_spec.spl` (2 new cases),
`test/01_unit/browser_engine/simple_web_html_layout_renderer_decl_apply_coverage_closure_spec.spl`
(`color-scheme:light dark`), existing `ws_handshake_spec.spl` (now green).

## Per-site result (fetch-only, then 800x600 render)

| site | fetch | bytes | render |
|---|---|---|---|
| example.com | OK ~20s | 577 | OK 115s; see gaps A-D |
| www.google.com | OK ~21s | 85,383 | OK 145s; mostly tofu boxes, overlapping text (E, F) |
| www.wikipedia.org | OK ~21s | 93,955 | did not finish in 1800s; no `[web-phase]` line at all (G) |
| news.ycombinator.com | OK ~21s | 34,764 | OK 1133s (static pipeline 35.7s); header row scattered, story list missing (I) |
| github.com | OK ~21s | 576,688 | did not finish in 1800s; no `[web-phase]` line at all (G) |

Text mode (`main.spl https://<site>`) for the three big sites also exceeds
600s, because text mode runs the same engine render for its proof line.

## Open rendering gaps (unblock condition per item)

- **A. FIXED (work/browser-layout-width).** Not an inheritance bug:
  `text-align` inherits fine and the CPU raster path aligned lines, but the
  Draw IR text emitters (`simple_web_html_layout_renderer_paint_layout.spl`)
  drew every line at the content-box left edge. They now place each line
  with the raster path's `text_line_aligned_x` and width model.
- **B. FIXED.** `margin:auto` centring only considered an explicit `width`;
  a width:auto box clamped by `max-width` now shares the free space
  (`simple_web_html_layout_renderer_layout_engine.spl`).
- **C. FIXED.** `min-width`/`max-width` were read with `parse_int`
  (26em -> 26px); em now uses the element's font-size and rem the 16px root
  (`simple_web_html_layout_renderer_decl_apply.spl`).
  Spec for A/B/C: `test/01_unit/browser_engine/simple_web_width_centering_spec.spl`.
- **D. `padding:25vh 2em 2em` (3-value shorthand / vh) ignored** —
  **FIXED except % (work/browser-padding-units).** `_padding_integer_px`
  accepted only integer px/0 and one unsupported token dropped the whole
  declaration. Padding tokens now take em (element font size), rem (16px),
  and vw/vh resolved at computed-value time from the cascade pass's
  viewport: `compute_styles(..., viewport_w, viewport_h)` sets it for that
  pass only (cleared after; part of the cascade memo key), the render entry
  points pass their width/height, and with no viewport a vw/vh declaration
  is dropped exactly as before. Spec:
  `test/01_unit/browser_engine/simple_web_padding_units_spec.spl`.
  **Still open: percent padding** (relative to the containing block's WIDTH,
  which only layout knows); `padding: 10%` is still dropped. Unblock: resolve
  a percent sentinel per child in the block/flex/table layout paths and have
  paint read the layout-resolved padding.
- **D2. Author sheet ignored on the BrowserSession lane** — example.com
  carries `<script src=/s.js>`, so `browser_document_needs_session` routes it
  through BrowserSession, and the 800x600 render shows white background and
  full-width text even though the same HTML through the static lane picks up
  the `html{background}` rule.
  **Root cause (2026-10-04, work/browser-script-stall):** the app's session
  lane (`render_adapter.browser_session_pixels_at_time`) calls `open_html`
  and renders immediately, but never services the session's subresource
  requests (`take_pending_request` / `commit_network_response`), so the load
  stays blocked on the external `/s.js` and `_finalize_active_load` — the
  only place that copies `load.stylesheet_html()` into `current_style_html`
  — never runs; `render_html_document()` then emits `<head>` with no
  `<style>`. Reproduced offline with the exact example.com markup:
  `current_style_html` is empty after `open_html`. Not fixed here: the
  correct fix is a network pump in the app lane with the hosted lane's
  request policy (`_hosted_fetch_mode`/headers/HSTS stripping in
  `src/os/hosted/hosted_web_content_session.spl`), which also starts
  executing remote scripts — a feature/security decision, not a contained
  fix. Unblock: share the hosted pump (or an equivalent policy owner) with
  `src/app/browser`.
- **E. Glyph baseline jitter** — glyphs with ascenders/descenders (i, t, d,
  l, f, h) are offset vertically from their neighbours on every page.
- **F. Non-Latin text renders as tofu** (google.com Korean locale page) and
  inline runs overlap ("I'm Feeling Lucky" drawn over other labels).
  **Tofu: FIXED (work/browser-cjk-fallback).** Root cause: font resolution
  preferred the host face (Helvetica on macOS) for every run that was not
  Arabic/Devanagari, so Han/kana/Hangul - even with `lang="zh"` - went to a
  face with no CJK glyphs. `font_renderer.spl` now checks the bound face's
  cmap coverage for CJK-range codepoints and re-resolves an uncovered run:
  Han/kana -> bundled Noto Sans/Serif SC; Hangul -> platform AppleGothic
  (`font_provider.browser_platform_hangul_faces`). Measured coverage: Noto
  Sans SC has Han+kana, no Hangul; AppleSDGothicNeo has all three but is
  CFF (`unsupported-sfnt-version` in the glyf rasterizer); AppleGothic.ttf is
  glyf with Hangul. **Open:** the repo bundles no Hangul-capable font (only
  a vendored rustdoc woff under `src/compiler_rust/vendor/deltae`), so on
  Linux/CI Hangul stays .notdef until a Korean face (e.g. Noto Sans KR) is
  added to the selected-font catalog. Also open: the bundled SC faces
  resolve to their thin master (`axes=wght=100`), so CJK runs render light.
  Overlapping inline runs: still open.
- **I. news.ycombinator.com table layout** — the orange header bar paints,
  but the nav cell's inline children land on three separate rows ("|"
  separators, links, "Hacker News" title), links are blue instead of the
  page's black `.pagetop a`, the logo image is absent, and none of the 30
  story rows render.
- **G. Large pages do not finish rendering** in 30 minutes under the
  interpreter. With `SIMPLE_WEB_PHASE_TRACE=1`, wikipedia/github never emit
  even `phase=parse`, so the stall is BEFORE the static pipeline — in
  BrowserSession `open_html`/script execution (both carry `<script>`), not
  style/layout. HN's static pipeline took 35.7s of its 1133s run. `main.spl` itself drops to the interpreter
  (`HIR lowering error: Cannot infer field type: struct 'TextMetrics' field
  'char_count'`), and documents with `<script>` go through BrowserSession
  script execution. Unblock: fix the TextMetrics JIT lowering (another lane
  owns the TextMetrics rename) and profile with `SIMPLE_WEB_PHASE_TRACE=1`.
  **Root cause found and fixed (2026-10-04, work/browser-script-stall):**
  `SIMPLE_INTERPRETER_CALL_TRACE=all` showed the session binding ~4
  elements/s; `SIMPLE_PERF_COUNTERS=1` and the code showed why. The JS
  engine's `ObjectStore` is a flat list of every property of every object,
  and `set_object_property`, `get_object_property`, `ObjectStore.get_property`
  and `get_object` each scanned ALL of it (a property write did two full
  scans: the frozen check and the existing-key lookup). `_bind_dom_node`
  does ~10 writes + several reads per element, so binding N elements cost
  O(N * total properties) = quadratic. Fix: `ObjectStore.prop_slot_index`
  ("{obj_id}:{key}" -> latest slot) and `obj_slot_index` (obj_id -> slots in
  ascending order), kept in sync on append and rebuilt on removal or
  compaction; lookups fall back to the old scan whenever the index does not
  cover every slot, so answers are identical. Pinned by
  `test/01_unit/lib/nogc_sync_mut/js/engine/object_store_slot_index_spec.spl`.
  Measured (same seed, same saved HTML, before = origin/main tree):
  `open_html` on a synthetic N-element scripted page 112.3s -> 3.5s at
  N=100 and 363.2s -> 9.5s at N=200; news.ycombinator.com full render
  1133-1922s -> ~130-270s (host load varied); github.com never finished in
  1800s -> 276-497s. example.com and google.com pixel checksums identical
  before/after.
- **K. www.wikipedia.org: C font SFFI not wired into the seed interpreter.**
  With G fixed, wikipedia reaches rendering and fails with
  `semantic: unknown extern function: rt_font_glyph_index` (multi-script
  fallback in `src/lib/skia/feature/shaper/font_fallback.spl:71`). Only
  `rt_font_load_array` is registered in
  `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`; the other 14
  `rt_font_*` externs of `src/lib/nogc_sync_mut/io/font_sffi.spl`
  (`rt_font_free`, `rt_font_glyph_bitmap`, `rt_font_bitmap_*`, ...) are
  implemented in `src/runtime/runtime_font.c` but unreachable from `run`.
  They take raw C pointers, so wiring them needs a handle owner on the Rust
  side (not just `insert_simple!`) to keep a stale or forged handle from
  becoming a use-after-free. Unblock: add that owner + the 15 externs.
- **J. github.com layout** — renders, but the nav menu's collapsed panels
  are laid out expanded and link/description columns overlap.
- **H. Stale deployed seed** — `/Users/ormastes/simple/bin/simple` predates
  `faa15917adc` (host `@when` stripping), so it cannot parse origin/main's
  `src/lib/nogc_sync_mut/io/windows_redirected_process.spl` ("expected Fn,
  found Colon") and every `run` of the browser fails on current main.
  Unblock: redeploy a seed built from current main.
