# BrowserSession re-requests an external classic script forever (2026-10-04)

Status: FIXED in branch `work/browser-subresource-pump`.
Parent record: `browser_real_site_rendering_gaps_2026-10-04.md` (gap D2).

## Symptom

A page with `<script src=...>` (example.com has one) never finished
loading in BrowserSession: the stylesheet was never applied, and inline
scripts after the external one never ran. In the app browser this showed up
as example.com rendering unstyled (white background, full-width text).

## Root causes

1. `src/lib/gc_async_mut/web/browser_session_loading.spl`
   `_advance_script_loading`: the external classic-script branch advanced
   `load.next_script_idx` on a COPY of the active load (`if val Some(load) =
   self.active_load`) and returned without storing it back. The wasm branch
   right above it stores back (`self.active_load = Some(load)`); the script
   branch did not. So every committed response (success OR failure) re-ran
   the same block and queued the same script again. Repro:
   `test/01_unit/app/browser/browser_subresource_pump_spec.spl` ("advances
   past an external script after a successful response / failed fetch").
2. `src/app/browser/render_adapter.spl` called `open_html` and rendered
   immediately; nothing serviced the session's request queue.

## Fix

- Store the advanced load back before queueing the script request.
- New `src/app/browser/subresource_pump.spl` drains the queue with the hosted
  lane's request rules, now shared from
  `src/os/hosted/hosted_browser_renderer_policy.spl`
  (`hosted_browser_fetch_mode` / `_fetch_headers` / `_has_cookie_header` /
  `_wasm_hex`, previously private copies in `hosted_web_content_session.spl`).
  Styles and images are fetched. Remote code (script, module, wasm) and
  script-initiated fetch() are completed as failed fetches ("blocked by
  policy") unless `SIMPLE_BROWSER_REMOTE_SCRIPTS=1`; document requests are
  refused.

## Still open (layout, not loading)

With the stylesheet applied, example.com is grey with the right font but is
still not centred and wraps one word per line: `max-width: 26em` is read as
26px (`decl_apply.spl` parses min/max-width with `parse_int`, no em/rem),
and `margin: auto` + `max-width` / inherited `text-align: center` are not
applied by layout (gaps A, B, C in the parent record).

## Security review of the pump (2026-10-05)

- Scheme: the pump admits only http/https subresource URLs
  (`browser_subresource_scheme_allowed`); anything else is committed as
  "blocked by policy: subresource scheme is not http/https" before any
  transport is touched. This matches what the hosted lane can carry (its
  runtime job and `h1_client` reject non-http(s) with "unsupported URL
  scheme"). Independently, BrowserSession never queues an https document's
  `file:///` stylesheet at all - it records
  `stylesheet load error: unsupported-scheme:file:///etc/passwd`
  (spec: "never loads an https document's file:/// stylesheet").
- Private network / localhost: the hosted lane has no extra block beyond the
  session's mixed-content rule (https document -> http subresource blocked,
  loopback http excepted); the pump inherits exactly that and adds nothing.
- Found while probing, NOT fixed here: `<link rel=stylesheet
  href="data:text/css,...">` is resolved as a RELATIVE URL
  (`https://example.com/data:text/css,...`) and fetched from the document's
  origin instead of being decoded inline. Same-origin http only, so not a
  data leak, but data: stylesheets never apply.

## data: URLs and image bodies (2026-10-05, work/browser-data-urls)

- FIXED: `resolve_relative_url` treats `data:` as absolute; `<link>`
  stylesheets and `<img>` images with data: URLs are decoded in the session
  (`browser_data_url_decode`, RFC 2397: media type, `;base64`, percent
  decoding) and never queued for a transport. CSP (`style-src`/`img-src`)
  still runs first; the 50 MiB resource limit applies to the decoded body.
  CSS `background-image: url(data:...)` is still excluded on purpose by
  `browser_session_html.spl` (unchanged).
- FIXED: image response bodies must cross into BrowserSession as lowercase
  hex (`_image_hex_bytes`); the sandboxed renderer process did that, but
  `hosted_web_content_session.spl` and the app subresource pump sent the raw
  bytes as text, so every network image failed with "invalid image payload".
  The shared helper is now `hosted_browser_binary_hex` and both hosts use it
  for `image` as well as `wasm`.
- Found, not fixed: inside `browser_session_loading.spl`, `byte.to_i64()
  .to_hex()` dispatched to a free `to_hex` colour helper (error "undefined
  field 'r' ... type 'i64'") instead of the integer method; the new
  `_image_bytes_hex` spells the hex out.
