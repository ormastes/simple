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

- **A. `text-align` on `body` not inherited to `<p>`** — text stays left.
  Repro: `body{text-align:center}` + `<p>`. Unblock: inherit text-align.
- **B. `margin:auto` with `max-width` does not center a block.**
  Repro: `body{max-width:200px;margin:auto}`.
- **C. `max-width:26em` resolves far too narrow** (one word per line at a
  400px viewport where 26em=416px). em units in max-width are mis-resolved.
- **D. `padding:25vh 2em 2em` (3-value shorthand / vh) ignored** — no top
  padding. Repro `body{padding:100px 2em 2em}` also ignored.
- **D2. Author sheet ignored on the BrowserSession lane** — example.com
  carries `<script src=/s.js>`, so `browser_document_needs_session` routes it
  through BrowserSession, and the 800x600 render shows white background and
  full-width text even though the same HTML through the static lane picks up
  the `html{background}` rule.
- **E. Glyph baseline jitter** — glyphs with ascenders/descenders (i, t, d,
  l, f, h) are offset vertically from their neighbours on every page.
- **F. Non-Latin text renders as tofu** (google.com Korean locale page) and
  inline runs overlap ("I'm Feeling Lucky" drawn over other labels).
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
- **H. Stale deployed seed** — `/Users/ormastes/simple/bin/simple` predates
  `faa15917adc` (host `@when` stripping), so it cannot parse origin/main's
  `src/lib/nogc_sync_mut/io/windows_redirected_process.spl` ("expected Fn,
  found Colon") and every `run` of the browser fails on current main.
  Unblock: redeploy a seed built from current main.
