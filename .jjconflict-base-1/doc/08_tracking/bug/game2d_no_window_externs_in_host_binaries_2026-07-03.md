# Gap: deployed bin/simple lacks window externs — game2d wrapper uses gui-feature driver when available

**Date:** 2026-07-03
**Component:** interpreter extern surface (`src/compiler_rust/compiler/src/interpreter_extern/`),
`src/lib/nogc_sync_mut/game2d/backend/sdl_backend.spl`, G3.3 real-window evidence.

## Symptom

The deployed self-hosted `bin/simple` rejects the window externs needed by the
real-window Breakout gate:

- `rt_sdl2_init` → `semantic: unknown extern function` in the interpreter.
  The `rt_sdl2_*` C implementations exist only in
  `src/runtime/runtime_sdl2.c`, which links into AOT-compiled artifacts —
  they were never added to the interpreter extern dispatcher.
- `rt_winit_event_loop_new` → same error in deployed `bin/simple`. The
  interpreter DOES have a full
  native winit+softbuffer window implementation
  (`interpreter_extern/winit_sffi/`, real windows, present, key events), but
  it is behind the `gui` cargo feature (`compiler/Cargo.toml: default = []`,
  `gui = ["winit", "softbuffer"]`) and deployed `bin/simple` was not built
  with it.

Current host evidence: `cargo check -p simple-compiler --features gui` and
`cargo build -p simple-driver --bin simple --features gui` pass. Under private
Xvfb, `src/compiler_rust/target/debug/simple` exposes
`rt_winit_event_loop_new` (`el=1`) and runs
`test/03_system/game2d/breakout_window_capture_spec.spl` with
`SIMPLE_BREAKOUT_WINDOW=1`: 1 example, 0 failures,
`window_frames_presented=12`.

## Impact

- G3.3's "real window capture of gameplay" leg can run on this host with the
  gui-feature Rust driver binary. Deployed `bin/simple` still records a host
  block. The AOT/JIT path for the game remains independently blocked (see
  `jit_game2d_backend_method_dispatch_sigsegv_2026-07-02.md`).
- Same block applies to W1/G1.1 (`examples/06_io/ui/widget_showcase_gui.spl`
  uses the identical `rt_winit_*` surface via `io/window_winit.spl`) — its
  ledger entry "G1.1 NOT RUN" is this gap, not just the live-display ban.
- The wrapper falls back to `src/compiler_rust/target/debug/simple` for the
  window leg when that gui-feature binary is present and proves the
  `rt_winit_*` surface.

## Current handling (recorded, not skipped)

- `SdlBackend` is wired to the `rt_winit_*` surface (the only window API
  with a real implementation anywhere in the tree).
- `test/03_system/game2d/breakout_window_capture_spec.spl` is env-gated on
  `SIMPLE_BREAKOUT_WINDOW=1` (set by `scripts/check/check-game2d-breakout.shs`
  only after probing extern availability). Without it, the spec records
  `window_backend=blocked_host` and asserts this gap doc exists; with the
  gui-feature driver it presents 12 real frames under Xvfb.

## Fix

Deploy a self-hosted `bin/simple` or CI binary with the `gui` feature, or keep
using the wrapper's gui-feature driver fallback for local evidence. Register
the `rt_sdl2_*` set in the interpreter only if SDL2 becomes the chosen window
surface again.
