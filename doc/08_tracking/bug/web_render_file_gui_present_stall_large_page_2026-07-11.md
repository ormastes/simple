# web_render_file_gui: window presents small pages but stalls on google.com page

- **Status:** Open
- **Date:** 2026-07-11
- **Area:** examples / ui (web_render_file_gui.spl present loop) + winit present path
- **Severity:** P2 (live-window lane unusable for real-world pages)

## Symptom

`scripts/gui/macos-gui-run.shs` + `web_render_file_gui.spl` (constants bumped
to 480x360):

- `hello_world.html` (small page): renders and PRESENTS on screen correctly
  (real window, content visible; captured 2026-07-11).
- live `google.com` HTML (82KB): app logs
  `Rendered 172800 px via requested backend 'cpu_simd'` after ~4 min
  (interpreted), but the window stays WHITE; process burns 90-98% CPU for 9+
  more minutes with no frame ever composited. Same pixel count as the hello
  case (480x360), so pack_pixels volume is identical — the stall is not the
  pack loop size.

## Repro

1. Fetch google.com HTML (e.g. via the FetchEngine probe) to a file.
2. Point `web_render_file_gui.spl`'s fallback path at it (cli_get_args is
   stubbed in the GUI driver — args do not reach the app; see below).
3. `SIMPLE_TIMEOUT_SECONDS=0 scripts/gui/macos-gui-run.shs <probe.spl>`.
4. Window appears, title correct, render completes per launch.out, no frame.

## Suspects / next steps

- Instrument the app's post-render path with `dbg_stage` (pack begin/end,
  present call, poll iteration) to find where it spins.
- Check winit_present_rgba return codes on the big-page path.

## Related blockers found in the same arc

- GUI driver (`CARGO_TARGET_DIR=target/gui cargo build --features gui`) stubs
  `cli_get_args` (`[STUB] cli_get_args not available without Rust SFFI`), so
  `.app`-bundle launches cannot pass file arguments — probes must hardcode
  paths. Worth a bug/feature of its own if the GUI driver is meant for real
  use.
