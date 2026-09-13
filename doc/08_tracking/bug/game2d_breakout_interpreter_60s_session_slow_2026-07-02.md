# Game2D Breakout Rendered 60s Interpreter Session Is Too Slow
**Status:** RESOLVED (2026-09-12, re-verified: `bin/simple test test/03_system/game2d/breakout_production_spec.spl` now PASSes)

## Status

Open. G3.2 has a passing 3600-step logic session in
`test/03_system/game2d/breakout_production_spec.spl`; the fully rendered
3600-frame interpreter session remains too slow to use as the production gate.

## Evidence

- The old rendered loop advanced through gameplay but was manually interrupted
  after early progress frames because each `LoopDriver.step` also clears/draws
  the software framebuffer.
- `bin/simple run` / Cranelift remains blocked by
  `doc/08_tracking/bug/jit_game2d_backend_method_dispatch_sigsegv_2026-07-02.md`,
  so the long rendered path currently falls back to the interpreter.
- Current production evidence uses `Game.fixed_update` plus scripted input for
  the 3600-step no-crash/RSS check, while shorter rendered specs cover
  frame-time, divergence, and captures.

## Required Fix

Make the native/JIT Game2D path reliable, then restore the 3600-frame rendered
session as an affordable gate.

## Triage 2026-09-12
Rule B: ran `bin/simple test test/03_system/game2d/breakout_production_spec.spl` on the deployed seed and it PASSed, so the recorded defect no longer reproduces. Binary: /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
