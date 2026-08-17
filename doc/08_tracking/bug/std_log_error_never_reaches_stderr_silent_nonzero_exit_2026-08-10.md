# `std.log.error(...)` never reaches stderr — commands exit non-zero SILENTLY

- **Status:** FIXED (`src/lib/log.spl`, `log_dispatch_text`)
- **Found:** 2026-08-10, alongside the `simple replay` fork-bomb sweep (Q15)
- **Severity:** High — this is the failure shape that HID the replay fork bomb

## Symptom

`src/app/replay/main.spl` reports its terminal failure with
`error("replay", "build-log replay is not yet implemented: {target}")` and
returns 1. The run exits 1 with **no output whatsoever**. Same for
`compile`, `web`, `run`, `gen-lean` and every other wrapper that reports
failure via `std.log.error`.

A silent non-zero exit is exactly the shape that hides this class of bug: the
`replay` self-spawn chain looked like "a build that mysteriously dies", and
three separate streams then hunted a nonexistent HIR-lowering memory leak.

## Root cause

`src/lib/log.spl::log_dispatch_text` interned the message and called
`_dispatch_to_backends`. The **only** backend implemented in the facade is
`kind == 1` (the in-memory ring buffer); `kind == 2` ("console") has no
implementation anywhere. stderr was written only under `_g_panic_mode`.

So `error()` wrote into a ring buffer that nothing drains on a CLI exit path.
The diagnostic was produced and then discarded. The in-file comment called
this "a documented decision, not a silent gap" — for a CLI entry point it is
precisely a silent gap.

Note this is NOT the `SIMPLE_LOG` level gate. `src/lib/nogc_sync_mut/log.spl`
has a *separate* level-gating bug of the same class (`_parse_log_level()`
returns 0 when `SIMPLE_LOG` is unset, so its `error`/`fatal` are also
suppressed by default) — that module was left unchanged here to keep the fix
scoped; it is a live follow-up.

## Fix

`log_dispatch_text` now writes to stderr when `_g_panic_mode` **or**
`level >= LOG_ERROR`. Levels below ERROR stay ring-only, so no log spam is
reintroduced.

## Evidence

Probe: `env SIMPLE_DELEGATION_DEPTH=9 ./bin/simple run src/app/web/main.spl
build z.spl`, which takes a terminal path that calls both `error(...)` and a
plain `eprint` carrying the same text.

| | occurrences of the message in captured output | exit |
|---|---|---|
| before | **1** (the `eprint` only — `error()` produced nothing) | 1 |
| after  | **2** (`error()` now surfaces too) | 1 |

Run under `systemd-run --user --scope -p TasksMax=12`.

## Related

- `doc/08_tracking/bug/simple_replay_self_spawns_unbounded_process_chain_2026-08-10.md`

## RESOLVED — residual also fixed (verified 2026-08-17)

The § Residual item (`src/lib/nogc_sync_mut/log.spl` `_parse_log_level()`
defaulting to LOG_OFF) is now fixed in source: `_DEFAULT_LOG_LEVEL = 2`
(LOG_ERROR) with `SIMPLE_LOG=off` as the deliberate opt-out, and the main fix
(`log_dispatch_text` writing ERROR/FATAL to stderr via `rt_stderr_write`) is
present in `src/lib/log.spl` lines 652-674. Nothing left open in this doc.

Spec coverage (2026-08-17): repro + generalization spec
`test/01_unit/lib/nogc_sync_mut/log_default_level_error_visible_spec.spl`
(mirrored in `test/unit/lib/nogc_sync_mut/`): pins the unset-SIMPLE_LOG default
to >= LOG_ERROR (pre-fix it was LOG_OFF), the severity ordering, and that
error()/fatal() execute the emission path. Green: 3 examples, 0 failures.
