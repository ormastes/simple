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
