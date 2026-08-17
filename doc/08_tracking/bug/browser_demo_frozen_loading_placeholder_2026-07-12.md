# browser_demo app is a frozen "Loading..." placeholder, not a browser

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Status

Open.

## Symptom

`browser_demo_hosted_main` (`src/os/apps/browser_demo/browser_demo_hosted.spl:15-35`)
calls `client.update_content(...)` exactly once, before entering its event
loop:

```
src/os/apps/browser_demo/browser_demo_hosted.spl:27
    client.update_content("SimpleOS Browser\n\nLoading: " + BROWSER_DEMO_START_URL + "\n\nWelcome to SimpleOS Web\nSimpleOS - The Simple Operating System\n")
```

The subsequent `while running:` loop (lines 28-32) only watches for
`WM_EVENT_CLOSE`; it never calls `update_content` again, never issues a
navigation/fetch, and never reacts to input. The window therefore displays
the literal text `"SimpleOS Browser\n\nLoading: https://simpleos.example.org/welcome..."`
for the entire lifetime of the app — a permanently frozen loading screen
presented to the user as a working browser.

## Production reach

This is not a dead code path — the app is registered end-to-end through the
SimpleOS app/launcher registry:

- `src/os/kernel/loader/app_registry.spl:151` — boot app entry
  (`canonical_path: "/sys/apps/browser_demo"`, `fat32_leaf: "BROWSMF.SMF"`,
  `boot_seed: true`).
- `src/os/kernel/loader/seeded_app_registry.spl:9` — seeded into the app list.
- `src/os/kernel/loader/builtin_binary_registry.spl:37` — resolves
  `"/sys/apps/browser_demo"` to a builtin binary.
- `src/os/services/launcher/launcher_registry.spl:214-215` — launcher-visible
  entries for `/sys/apps/browser_demo` and `/sys/apps/browser_demo.smf`.
- `src/app/hosted_apps/browser_demo_client.spl` — hosted client entry point
  that calls `browser_demo_hosted_main`.

A user launching "Browser" (browser_demo) from the SimpleOS launcher gets a
window that never renders any page content or reacts to navigation — it is
indistinguishable from a hung/broken app.

## Fix direction (not implemented here)

Two acceptable directions, either is sufficient:

1. **Real navigation**: wire `browser_demo_hosted_main`'s event loop to an
   actual fetch/render pipeline (e.g. the same Simple Web content-frame path
   used by `simple_web_content_frame_cached` /
   `render_simple_web_content`, `src/os/compositor/simple_web_window_renderer.spl`)
   so `update_content` is called again once `BROWSER_DEMO_START_URL` actually
   loads, and again on any subsequent navigation event.
2. **Demo-only labeling**: if real navigation is out of scope for this app,
   relabel it plainly as a static demo/placeholder (window title and body
   text) instead of presenting a permanently-loading "SimpleOS Browser", and
   remove or gate its launcher-visible "Browser" identity so it isn't
   confused with a working browser (the real browser path is
   `os.apps.browser` / the Simple Web renderer, not this demo app).

No navigation logic was implemented as part of filing this bug.

## Verification 2026-08-17 (content classification, fleet lane I)
STILL-OPEN, verbatim. `src/os/apps/browser_demo/browser_demo_hosted.spl:27` is
still a single static `client.update_content("SimpleOS Browser\n\nLoading: " +
BROWSER_DEMO_START_URL + ...)` call, and the body that follows it is only
`while running: val event = client.wait_event(); if event.event_type ==
WM_EVENT_CLOSE: running = false`. There is no fetch, no parse, no render, and
no second `update_content` anywhere in the file — the window shows "Loading:"
forever by construction. Not a defect to patch: making this a browser is a
feature build, out of scope for a silent-wrong-result lane.
