# Crash Debugging & Failure Visibility Guide

How to observe and debug task/actor/advice failures after the 2026-06-11
crash-hardening waves. Design rule: **failures never propagate across
task/actor/advice boundaries and never pass silently** — every catch records a
queryable reason. Diagnostics with per-call overhead are env-gated and
**default OFF** (`SIMPLE_<NAME>` set = on).

## What no longer crashes the process

| Failure | Old behavior | New behavior |
|---------|-------------|--------------|
| Task panic in executor worker | worker thread died; queued tasks abandoned; join error swallowed | caught; `[simple-executor] task <id> panicked: <msg>` on stderr; worker continues; message queryable via `take_last_task_panic()` (Rust) |
| Actor body panic | `rt_actor_join` returned bare 0 | reason recorded at panic time; `rt_actor_join` logs it; `rt_actor_death_reason(actor)` returns the message (NIL if alive/clean) |
| `join_actor(id)` (scheduler) | always silently succeeded without joining | performs a REAL join via shared handle; failure carries the death reason |
| Panic while holding a global registry lock (`concurrent` map/queue/pool/stack/tls) | poisoned mutex cascaded panics process-wide | poison recovered (`into_inner`); process survives |
| AOP around-advice panic (incl. proceed ≠ exactly once) | silent NIL return | NIL return preserved for ABI, plus stderr line and `rt_aop_last_error()` / `rt_aop_clear_last_error()` |
| Advice `Err` denying a join point | operation silently dropped when caller ignored the Result | denial recorded: `aop_denial_count()`, `aop_last_denial()`, `aop_clear_denials()` (std.nogc_sync_mut.src.aop) |
| Scheduler task failure (.spl HostScheduler) | task vanished | death record (task key + reason) kept; `last_death_reason()` / `death_count()`; sibling tasks keep running; `HostTaskHandle.error` populated for Result tasks |
| Actor handler dispatch error (.spl ActorScheduler) | `DispatchResult` discarded | per-actor `actor_error_count(id)` / `actor_last_error(id)`; scheduling continues |
| `send` to closed channel | silent no-op only | `try_send` reports closed; `is_closed()`; GreenChannel gained `close()` / `close_drain()` that wakes parked receivers (no permanent parking) |
| `await` on an eager (non-Future) value | NIL bit pattern leaked (printed as 3) or semantic error | identity — returns the already-resolved value in both JIT and interpreter modes |

## Env toggles (presence = on, default off)

| Flag | Effect | Overhead when off |
|------|--------|-------------------|
| `SIMPLE_ACTOR_TRACE` | per-message log line on actor handler dispatch errors | none (flag read once at scheduler construction) |
| `SIMPLE_EXECUTION_MODE` | `interpret` / `cranelift` / `llvm` — pin the execution path when bisecting a JIT-vs-interpreter divergence | none |
| `SIMPLE_RESOLVER_TRACE` | module resolution tracing | none |

All always-on recording above is failure-path-only: zero allocation and zero
extra work when nothing fails.

## Debugging recipes

- **A spawned task's result never arrives:** check `last_death_reason()` on the
  HostScheduler / `take_last_task_panic()`; the task key embeds
  `scheduler-task-<id>` / `runtime-task-<id>` from
  `current_unified_task_key()`.
- **An actor stopped responding:** `rt_actor_is_alive`, then
  `rt_actor_death_reason` for the panic message; for handler-level errors use
  `actor_error_count` / `actor_last_error`.
- **An operation guarded by AOP advice didn't happen:** `aop_denial_count()`
  rising means advice denied it — `aop_last_denial()` names the join point,
  advice kind, and error.
- **Interpreter and native disagree:** rerun with
  `SIMPLE_EXECUTION_MODE=interpret` vs `cranelift` to isolate the layer before
  filing the bug (`bin/simple bug-add`).

## Related

- Plan: `doc/03_plan/runtime/hardening_formal_verification_2026-06-11.md`
- Research: `doc/01_research/runtime/crash_hardening/crash_surface_bug_lean_research_2026-06-11.md`
- Formal models: `src/verification/aop_weaver/`, `src/verification/gc_boundary/`
  (+ kernel_capabilities / actor_channel / db_storage as they land);
  `scripts/check/check-lean-proofs.shs` builds all Lean projects, zero-sorry gate.
