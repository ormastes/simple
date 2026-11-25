# Game2D Breakout Rendered 60s Interpreter Session Is Too Slow
## Open 2026-09-16 — needs owner triage
## Triage 2026-11-25 — still OPEN, blocked on JIT Game2D reliability (large program)

2026-11-25 triage (work/p3-baq-20261125): the required fix is unchanged —
make the native/JIT Game2D path reliable (tracked by
`jit_game2d_backend_method_dispatch_sigsegv_2026-07-02.md`), then restore the
3600-frame rendered session as an affordable gate. That is a JIT backend
program, not a bounded pure-Simple fix verifiable on this Windows host within
a bug-ledger pass. Left OPEN; no doc content changed beyond this note.

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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

