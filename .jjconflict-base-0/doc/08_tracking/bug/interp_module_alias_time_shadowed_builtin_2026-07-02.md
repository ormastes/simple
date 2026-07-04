# Interpreter: `use <module> as time` alias unresolvable — "variable `time` not found"

Date: 2026-07-02
Status: open (workaround in place)
Severity: P2
Related: game2d headless run path

## Symptom

Aliasing a module import to the name `time` makes every call through the alias
fail at runtime under `bin/simple run` (interpreter path):

```simple
use std.nogc_sync_mut.game2d.time.det_guard as time
...
time.set_deterministic_mode(true)   # error: semantic: variable `time` not found
```

Renaming the alias (e.g. `as det_time`) with no other change resolves it, so
the alias mechanism itself works — the name `time` is special-cased or
shadowed (likely by the builtin `time` module) during interpreter resolution.

## Repro (verified 2026-07-02)

Before the rename, any game2d example hit it at startup:

```bash
env SIMPLE_GAME_HEADLESS=1 bin/simple run examples/11_advanced/game2d/breakout/main.spl
# error: semantic: variable `time` not found
```

## Workaround

`src/lib/nogc_sync_mut/game2d/app/run.spl` and
`src/lib/nogc_sync_mut/game2d/loop/driver.spl` now alias as `det_time`.

## Expected

A local `use ... as X` alias should win over (or at least be resolvable
alongside) any builtin module named `X`, or the collision should be a
compile-time error — not a runtime "variable not found".
