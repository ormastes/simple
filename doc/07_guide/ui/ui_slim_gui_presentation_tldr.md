# UI-slim GUI presentation gate — TL;DR

```bash
cp src/runtime/spl_winit/target/release/libspl_winit.dylib build/sffi/   # once
sh scripts/check/check-ui-slim-gui-present.shs --out /abs/g1.ppm
sh scripts/check/check-ui-slim-gui-present.shs --selftest   # selftest: 4/4 passed
```

* **Fixture:** `test/05_perf/ui_slim/g1_greeting_gui.spl` — builder tree
  (greeting + button) -> DrawIR v2 -> v3 -> `ScreenGuiHost` -> `GuiRenderer`
  (dlopen'd winit cdylib). Existing route; nothing hand-drawn, nothing patched.
* **Launcher:** `scripts/gui/macos-gui-run.shs`, which selects the only
  winit-marked driver here, `bin/release/aarch64-apple-darwin/simple`. The Rust
  seed is refused by that script. No compiler is built.
* **Gotcha:** `open -n` gives cwd `/` and drops `SIMPLE_SPL_WINIT_PATH`; the
  check exports `DYLD_LIBRARY_PATH=<repo>/build/sffi` so the dlopen resolves.
* **Clock:** both sides use CLOCK_REALTIME (`gdate +%s%N` outside,
  `time_now_unix_micros()*1000` inside). Not monotonic.
* **Oracle:** the P6 PPM of the buffer given to `present_argb_u32` — never a
  screenshot. The greeting rect must differ from the background **and** hold
  >= 2 distinct colours.
* **Verdict (last stdout line):** `PASS — window presented, <k> milestones, ppm
  non-blank` / `FAIL` / `ERROR — nothing was checked (...)`; exit 0/1/2. No
  `window_created` = FAIL even on exit 0.
* **Measured 2026-09-06 (240x140, interpreted):** entry 5401 ms, window 5695 ms,
  first submission 10428 ms, input_ready 12699 ms, input->response 2726 ms.

Full guide: `ui_slim_gui_presentation.md`.
