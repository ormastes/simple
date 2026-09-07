# Slim-UI GUI reference fixtures — TL;DR

Full guide: [`ui_slim_gui_references.md`](ui_slim_gui_references.md) · A09, 2026-09-06

- **Two categories, never merged.** `widget-core-headless` (microui, Nuklear:
  widget core on a scripted input feed, draw commands counted, no window) vs
  `visible-window` (FLTK: real window). Design §4 [W07].
- **microui** `0850aba86` — 1500 draw cmds/run, **0.0495 ms** median (10 runs),
  51,864 B stripped, 0 warnings.
- **Nuklear** `e3e18dc1e` — 1000 draw cmds/run, **0.0810 ms** median (10 runs),
  226,168 B stripped, 2 upstream unused-function warnings (recorded, not
  suppressed).
- **FLTK = `unsupported`.** Not installed; A09 forbids installing. `run.shs`
  re-probes 4 locations and exits 2 `ERROR — nothing was checked`. No `main.cpp`
  exists — no fake, no substitute.
- **Diagnostic only. Zero comparison against Simple.** 1500 vs 1000 commands is
  different frame *decomposition*, not efficiency; 50 µs vs 81 µs is
  `INCONCLUSIVE` (inside run-to-run spread). Draw commands are not pixels; binary size is not RSS.
- **Each run asserts 4 things:** 100 frames, greeting in the draw stream on
  every frame, `submit_count >= 1` (the scripted click actually hit the button —
  a missed click still emits a full frame), and a run-to-run identical command
  count. Sabotage selftest (`-DSABOTAGE_NO_GREETING`) runs first and is fatal.
- **macOS limits:** Apple clang 17.0.0 (not upstream LLVM 23), no FLTK, no
  `/proc`/smaps/PSS, no runner lock, synthetic 8×16 font metrics, 10 runs is a
  pilot not §8.5's 100.
- Receipts: `build/ui_slim/ref/<name>.receipt.sdn`. Vendored upstream +
  verbatim licenses: `test/05_perf/ui_slim/ref/vendor/<lib>/README.md`.
- Sibling guide, **different owner**: `ui_slim_c_references.md` (termbox2,
  ncursesw — A08). Do not edit.
