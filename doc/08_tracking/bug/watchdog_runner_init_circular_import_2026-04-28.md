# Watchdog kill — early-init / circular import (slow_run line 1257) — 2026-04-28

Cross-ref: `.sstack/fix-perf-bugs/timeout_triage.md` (kill #1, line 1257)
and sibling triage `doc/08_tracking/bug/dsl_spec_wedge_2026-04-27.md`
(runner-attribution bug — same root cause).

## TL;DR

The first watchdog kill in `--only-slow` was logged just before the line
`Circular import detected, returning empty dict (no partial exports yet) path="/home/ormastes/dev/pub/simple/src/app/ui/__init__.spl"`
and just after a flood of WARN
`Export statement references undefined symbol name=wire_writer_le / wire_reader_new / TextMode / translate_write / WireWriter / WireReader / recv_bytes_u32 / ...`
from `interpreter::interpreter_module::module_evaluator::evaluation_helpers:653`.

The kill is **NOT** an infinite loop in `module_loader.rs:474` — the
`Circular import detected` branch at that line correctly bails (`return Ok(empty Dict)`)
and decrements load depth.  Instead the kill is the same runner-observability
issue identified in `dsl_spec_wedge_2026-04-27.md`: the watchdog records crashes
against a single parent PID with no spec name, so the "spec at the moment of
fire" is a heuristic guess based on stderr proximity.

## Symptom

slow_run.stderr line 1257:
```
[watchdog] wall-clock timeout (60s) exceeded
[watchdog] crash report: .simple/logs/crash_3709914.log
... Circular import detected, returning empty dict (no partial exports yet)
    path=".../src/app/ui/__init__.spl"
```

## Root-cause class

`unknown / runner-observability` — could be either:
1. **Genuinely-slow spec just-before-kill** — `app.ui.__init__` transitively
   loads `common.ui.widget`, `common.ui.parse.sdn_tree`, `common.ui.layout`,
   `common.ui.state`, plus `nogc_sync_mut/platform/{mod,wire,__init__}.spl`
   (the source of the `wire_writer_*` warns). On a cold cache this can be
   genuinely slow on the interpreter (no hang), or
2. **Misattributed**: the kill belongs to a different earlier-running spec,
   and the `app/ui/__init__.spl` circular-import line happens to print right
   afterwards because the runner restarted module loading after the watchdog
   blow-up.

## Reproduction

Cannot reproduce as a hang in isolation. The stale triage stderr is the
only artifact. To confirm the loader path:

```bash
timeout 60 bin/simple --interpret -e 'use app.ui.*' 2>&1 | tail -20
```

If this completes < 5 s, the kill is misattribution (runner bug). If it
hangs, file a separate `app.ui.__init__ load storm` bug.

## Proposed fix shape

Block on the underlying runner-observability bug from
`dsl_spec_wedge_2026-04-27.md`:
- Watchdog crash log must record `spec=<path>` and `it=<name>` of the
  currently-monitored test.
- Add a `WORKER N: starting <spec>` banner before each test so stderr
  attribution is unambiguous.

Once observability lands, re-run `--only-slow` and re-classify this kill.

## Workaround

None required — the `Circular import detected` branch already returns an
empty dict and decrements depth; it is not the source of any hang. The
`Export references undefined symbol` WARN flood is benign noise from
exports declared on partial-export fallbacks.

## Status

OPEN — blocked on watchdog spec-attribution fix (see
`dsl_spec_wedge_2026-04-27.md` recommendation 1).
