# Gap: no window externs in any available binary — game2d real-window gate host-blocked

**Date:** 2026-07-03
**Component:** interpreter extern surface (`src/compiler_rust/compiler/src/interpreter_extern/`),
`src/lib/nogc_sync_mut/game2d/backend/sdl_backend.spl`, G3.3 real-window evidence.

## Symptom

Both available binaries reject every window extern:

- `rt_sdl2_init` → `semantic: unknown extern function` (seed AND deployed
  `bin/simple`). The `rt_sdl2_*` C implementations exist only in
  `src/runtime/runtime_sdl2.c`, which links into AOT-compiled artifacts —
  they were never added to the interpreter extern dispatcher.
- `rt_winit_event_loop_new` → same error. The interpreter DOES have a full
  native winit+softbuffer window implementation
  (`interpreter_extern/winit_sffi/`, real windows, present, key events), but
  it is behind the `gui` cargo feature (`compiler/Cargo.toml: default = []`,
  `gui = ["winit", "softbuffer"]`) and neither the seed at
  `src/compiler_rust/target/release/simple` nor the deployed self-hosted
  `bin/simple` was built with it.

## Impact

- G3.3's "real window capture of gameplay" leg cannot run on this host at
  all: no interpreter window path, and the AOT/JIT path for the game is
  independently blocked (see
  `jit_game2d_backend_method_dispatch_sigsegv_2026-07-02.md`).
- Same block applies to W1/G1.1 (`examples/06_io/ui/widget_showcase_gui.spl`
  uses the identical `rt_winit_*` surface via `io/window_winit.spl`) — its
  ledger entry "G1.1 NOT RUN" is this gap, not just the live-display ban.
- This host cannot rebuild the seed with `--features gui` (LLVM Polly
  missing — see `bootstrap_pure_simple_stage2_stall_yoon_note` note).

## Current handling (recorded, not skipped)

- `SdlBackend` is wired to the `rt_winit_*` surface (the only window API
  with a real implementation anywhere in the tree); it runs as soon as a
  gui-featured binary lands.
- `test/03_system/game2d/breakout_window_capture_spec.spl` is env-gated on
  `SIMPLE_BREAKOUT_WINDOW=1` (set by `scripts/check/check-game2d-breakout.shs`
  only after probing extern availability); without it the spec records
  `window_backend=blocked_host` and asserts this gap doc exists — same
  convention as the G5.2 Android-emulator host block.

## Fix

Build the seed (or CI binary) with `--features gui`, or register the
`rt_sdl2_*` set in the interpreter extern dispatcher. Then set
`SIMPLE_BREAKOUT_WINDOW=1` and the full window+xwd capture leg activates.
