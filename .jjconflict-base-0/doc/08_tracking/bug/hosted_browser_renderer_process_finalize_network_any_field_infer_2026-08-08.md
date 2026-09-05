# Bug: hosted_browser_renderer_process.spl native build fails — cannot infer field type on `struct 'ANY' field 'message'`

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).
now produces `wm_production_fullscreen_native_artifact=present` and zero
occurrences of "cannot infer field type" / "struct 'ANY'" in its output —
the native build genuinely succeeds now. See Resolution below. The guard
still exits 1 for an unrelated, later-stage reason (windowed/fullscreen
capture and snapshot evidence report `missing`) — that is a separate
concern, not this bug, and needs its own investigation before
`check-wm-host-css-override-evidence.shs`/`check-wm-production-fullscreen-evidence.shs`
can be wired into pre-push or CI.

**Found**: 2026-08-08, via `scripts/check/check-wm-host-css-override-evidence.shs` (an unwired guard under triage in the guard-wiring campaign).

## Symptom

`check-wm-production-fullscreen-evidence.shs` (the canonical baseline this guard reuses) fails the native build of `src/os/hosted/hosted_entry.spl`, which pulls in `src/os/hosted/hosted_browser_renderer_process.spl`:

```
Build failed: lower security registry source
/home/ormastes/dev/pub/simple/src/os/hosted/hosted_browser_renderer_process.spl:
Unsupported feature: cannot infer field type while lowering
HostedBrowserRendererProcess._finalize_network: struct 'ANY' field 'message'
```

Preceding warning in the same run:
```
Failed to load imported types from ["os", "hosted", "hosted_browser_render_evidence"]: cannot resolve import: module path segment 'os' not found
```

Logs: `build/wm-host-css-override-evidence/baseline/native-build.log`,
`build/wm-host-css-override-evidence/baseline/driver.stdout`,
`build/wm-host-css-override-evidence/baseline/report.md`.

## Impact

- Blocks `hosted_entry.spl`'s native build entirely, which in turn blocks
  `check-wm-production-fullscreen-evidence.shs` and
  `check-wm-host-css-override-evidence.shs` from reaching their actual
  CSS-override / pixel-diff assertions — the guard fails at build, before its
  real logic even runs.
- Not environmental/host-contention: the process ran to a definitive compiler
  error message, not a timeout.

## Suspected cause (not yet root-caused)

`HostedBrowserRendererProcess._finalize_network` in
`src/os/hosted/hosted_browser_renderer_process.spl` assigns/reads a `message`
field on a value the lowering pass sees typed as `ANY`, and cannot infer a
concrete field type for it. Likely related to the preceding import-resolution
warning for `["os", "hosted", "hosted_browser_render_evidence"]` — if that
module fails to resolve, a type that would normally narrow the `ANY` may be
unavailable, leaving the field's static type ambiguous.

## Resolution

Two distinct root causes, not one causally-linked chain as first suspected:

1. **Missing module.** `src/os/hosted/hosted_entry.spl` imports
   `os.hosted.hosted_browser_render_evidence` (`hosted_browser_html_css_evidence`,
   `hosted_browser_animation_evidence`, both actually called), but that
   module never existed on `main` — authored on a side branch, deleted
   there in `f119f8b7120`, never merged; a later sync commit added the
   import without the file. Restored verbatim from git history at
   `f119f8b7120^:src/os/hosted/hosted_browser_render_evidence.spl`.

2. **Elided `Result<T>` error-type argument.** `_finalize_network`'s error
   chain flows through `fetch.spl`'s `finalize_single_hop` and
   `h1_client.spl`'s `H1Client.request`, both of which declared
   `Result<FetchResponse>` (single type-arg) instead of
   `Result<FetchResponse, BrowserError>`. Native HIR lowering doesn't
   back-infer the elided error type from `Err(...)` construction sites, so
   `error.message` erased to `ANY`. Every `Err(...)` in both files
   consistently constructs `BrowserError` via `network_error()`/
   `parse_error()`, so pinning the explicit type was safe. Fixed in
   `src/lib/gc_async_mut/gpu/browser_engine/net/fetch.spl` (11 sites,
   commit `2c62f5cb028`) and `.../net/h1_client.spl` (6 sites, commit
   `b061a8929c2`).

Verified: `sh scripts/check/check-wm-production-fullscreen-evidence.shs`
no longer reports the "cannot infer field type" error and produces a real
native artifact.
