# JIT lowering: nested fn inside impl method unresolvable ("Unknown variable: clamp_f")

Date: 2026-07-02
Status: open (workaround in place)
Severity: P3 (silent fallback to interpreter — large perf cliff)
Related: doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (W5)

## Symptom

Every program importing the 2D engine color path fails JIT compilation and
silently falls back to the interpreter:

```
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering
error: Unknown variable: clamp_f while lowering EngineColor.to_rgba8
```

`clamp_f` resolves fine in interpreter mode. Root cause: `clamp_f` was a
**nested `fn` defined inside `to_rgba8` within an `impl` block** — HIR
lowering does not register nested fns in method bodies, so any nested-fn
call site fails JIT for the whole program. General bug: applies to every
nested fn inside an impl method, not just this one.

## Workaround

Hoisted the helper to module level as `_clamp_channel` in
`src/lib/common/engine/color.spl` (2026-07-02).

## Impact

All game2d examples (breakout, asteroids, pool, ...) and anything using
`EngineColor` run interpreted. Measured cost: one 800x600 breakout frame
takes >60 s interpreted; the W5 "60 s automated play session" gate is
unreachable until JIT works or the interpreter path gets much faster.

## Repro (verified 2026-07-02)

```bash
env SIMPLE_GAME_HEADLESS=1 bin/simple run examples/11_advanced/game2d/breakout/main.spl 2>&1 | grep clamp_f
```
