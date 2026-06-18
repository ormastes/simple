# Simple Web Browser Production Hardening Architecture

<!-- codex-design -->

This top-level architecture artifact is the canonical pipeline entry for the
Simple Web browser production hardening lane.

The detailed architecture is maintained at:

- `doc/04_architecture/ui/simple_web_browser_production_hardening.md`

That UI architecture note defines the production browser boundary, fail-closed
auth model, renderer evidence gate, hot request paths, startup behavior,
invalidation constraints, and release targets for selected Feature Option C and
NFR Option C.

Current local browser-surface evidence covers authenticated normal-server
`/api/state` and `/api/widgets` `200 OK` JSON responses plus normal and
shared-WM live routes for `/wm.js`, `/retained_renderer.js`, shown
`/wm/native_window`, and the unknown-route JSON `404 not_found` fallback. The
generated live endpoint manual records the corresponding no-store/no-cache/nosniff
and HTML CSP/frame/referrer header checks; external native rendering readback
remains a separate host-gated follow-up.

Keep this file as the stable pipeline path required by the self-sufficient
feature flow; update the detailed UI architecture note for substantive
architecture changes.
