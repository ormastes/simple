# Diagnostics (`std.diag`) Feature Expert

## Role

Own feature-specific process knowledge for `std.diag`, the shared easy-debug
infrastructure: a stage tracer, a cooperative (thread-free) watchdog,
aggregating timers/counters, an event-chain tracer, and an always-on
provenance assert. It targets five previously-undiagnosable problem classes
from this repo's real history: silent hangs, quadratic/slow paths found only
by wall-clock pain, silent GPU-to-software fallbacks, vanished event chains,
and cross-lane pixel diffs. This is P0 of the UI-test-infra plan — see the
[ui_testing](../ui_testing/skill.md) feature expert for the consumer (P1-P6,
not yet implemented).

## Pipeline Links

- [verify skill](../../../../.claude/skills/verify/SKILL.md)
- [spipe skill](../../../../.claude/skills/spipe.md) — "UI-lane specs &
  diagnostics" section covers spec-writing usage.

## Feature Links

- Module (owned, single file): [src/lib/nogc_sync_mut/diag.spl](../../../../src/lib/nogc_sync_mut/diag.spl)
  — import as `use std.diag.{dbg_stage, ...}`.
- Guide: [doc/07_guide/infra/debugging/easy_debug_infra.md](../../../../doc/07_guide/infra/debugging/easy_debug_infra.md)
- Design contract (owner of the stderr line formats and API shape):
  [doc/05_design/ui/testing/ui_test_infra_design.md](../../../../doc/05_design/ui/testing/ui_test_infra_design.md)
  §8 (§8.2 = exact contract; do not change stderr formats without updating it).
- Plan (P0 status + acceptance criteria):
  [doc/03_plan/ui/testing/ui_test_infra_plan.md](../../../../doc/03_plan/ui/testing/ui_test_infra_plan.md)
  "P0 — std.diag debug primitives".
- Spec (13/13 passing, the usage reference):
  [test/01_unit/lib/nogc_sync_mut/diag_spec.spl](../../../../test/01_unit/lib/nogc_sync_mut/diag_spec.spl)
- Consumer (designed, not implemented): [ui_testing feature expert](../ui_testing/skill.md).

## API Surface (exact names — `diag.spl`)

- Stage tracer: `dbg_stage(component, stage)`, `dbg_stage_history() -> [StageEntry]`,
  `dbg_stage_dump()`, `dbg_stage_on() -> bool`. Emits
  `[<component>] stage <stage> +<delta_ms>ms`; ring cap 256.
- Watchdog (cooperative, no threads): `dbg_deadline(label, budget_ms)`,
  `dbg_deadline_check(label) -> bool` (also auto-checked inside `dbg_stage`),
  `dbg_deadline_clear(label)`, `dbg_deadline_breach_count() -> i64`,
  `dbg_last_breach() -> text`, `dbg_deadline_active_count() -> i64`. Breach
  fires exactly once, emitting a multi-line `DEADLINE EXCEEDED` block plus the
  recent stage history. Composes `std.failsafe.timeout.Deadline` — no second
  deadline type.
- Timers/counters: `dbg_time_begin(label)`, `dbg_time_end(label)`,
  `dbg_count(label, delta)`, `dbg_timer_stats(label) -> DiagTimerStats`,
  `dbg_counter_value(label) -> i64`, `dbg_summary() -> text`,
  `dbg_summary_dump()`, `dbg_timers_on() -> bool`.
- Event-chain tracer: `dbg_event_hop(chain_id, hop, detail)` (guard expensive
  `detail` construction with `dbg_events_on() -> bool` in hot loops). Emits
  `[event <chain_id>] <hop> <detail>`.
- Provenance assert (ALWAYS ON, not env-gated): `dbg_provenance(claimed, actual,
  context) -> bool`, `dbg_provenance_mismatches() -> i64`,
  `dbg_last_mismatch() -> text`. Mismatch emits
  `DIAG-PROVENANCE context=<c> claimed=<x> actual=<y>` unconditionally.
- Test-only hooks: `dbg_force_facet(facet)` (forces a facet on mid-process —
  `SIMPLE_DIAG` is read once and cached, so env changes mid-spec are
  invisible), `dbg_diag_reset()` (clears all module state, use between `it`
  blocks), `dbg_last_emit() -> text` (last emitted line, `""` if none).
- Env gating: `SIMPLE_DIAG` = `all` or comma list of `stage,watchdog,timers,
  events`, read once at first use, zero-cost when unset. Emits through
  `lib.log`'s `log_dispatch_text` (backends observe diag lines) plus a direct
  stderr write (the facade only reaches stderr in panic mode).

## Gotchas (interpreter landmines proved during this work)

1. `if val Some(x) = dict.get(k):` **silently never matches.** `Dict.get()`
   returns the raw value or `nil`, not a `Some(..)`-tagged Option. Use
   `dict.get(k) ?? default` or `!= nil`. This bit the module's own
   implementation during development — see
   [interp_dict_get_option_match_never_matches_2026-07-05.md](../../../../doc/08_tracking/bug/interp_dict_get_option_match_never_matches_2026-07-05.md).
2. **Module globals mutated inside functions are stale when read directly
   from a spec `it` block** — always assert via the module's accessor
   functions (`dbg_last_emit()`, `dbg_timer_stats(...)`,
   `dbg_provenance_mismatches()`, etc.), never a raw module-level `var` read.
   See [interp_module_global_stale_read_in_spec_blocks_2026-07-05.md](../../../../doc/08_tracking/bug/interp_module_global_stale_read_in_spec_blocks_2026-07-05.md).
3. Subscript-assign on module-global dicts from another function
   (`d[k] = v`) does not persist — use `.set(k, v)`.
4. Named `diag`, deliberately NOT `dbg`/`debug` — avoids colliding with the
   existing interactive debugger modules (`nogc_sync_mut/debug.spl`, `debug/`).

## What's designed vs implemented

- **Implemented (P0, DONE):** everything in "API Surface" above, landed at
  `src/lib/nogc_sync_mut/diag.spl`, 13/13 specs green.
- **Designed, not yet implemented:** first production instrumentation sites
  (`ui.browser/app.spl`+`backend.spl` stage points, `hosted_entry.spl`,
  compositor frame loop) and the P1-P6 UI test infra that consumes this
  module as its hang/slow-path detector — see
  [ui_testing feature expert](../ui_testing/skill.md).

## Update Rule

After research, requirements, architecture, design, implementation,
verification, or release work changes this feature area, add or refresh
links here BEFORE committing, so the next agent starts from the current
project state.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`
