# Bug: hosted_browser_renderer_process.spl native build fails — cannot infer field type on `struct 'ANY' field 'message'`

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

## Next step

Read `_finalize_network` in `hosted_browser_renderer_process.spl` and the
`hosted_browser_render_evidence` module resolution path; fix the import
resolution first (module path segment `os` not found) since it may be the
root cause, then re-check whether the field-type inference error persists.
