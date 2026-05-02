# GAME-DET-LINT-001: Compile-time lint for `#[deterministic]` guard

**Priority:** low
**Filed:** 2026-04-25
**Code:** GAME-DET-LINT-001
**Component:** linter / `std.game2d` determinism guard
**Discovered by:** game2d-framework SStack Phase 3 architecture (deferred per User Decision 3)

## Description

The current `std.game2d` determinism implementation ships a **runtime guard**:
`g.time.now()` and `g.random.rand()` panic with `GAME-DET-001` when called
outside an active `App` callback while `deterministic_mode` is set
(`game2d/time/det_guard.spl`). This catches violations at replay time.

Phase 1 User Decision 3 explicitly deferred the **compile-time lint rule** —
a static check that flags raw `std.io.time.*`, unseeded RNG, and unordered
iteration calls inside any `App` callback annotated `#[deterministic]`.

## Why deferred

- Runtime guard alone closes the AC-4 invariant for the `App` callback path.
- A compile-time rule needs lint-rule infrastructure for `#[deterministic]`
  attribute-driven scoping, which is broader work than this iteration.
- `g.time.now()` / `g.random.rand()` wrappers are the canonical path; raw
  `std.io.time.*` outside `g.*` bypasses the guard intentionally — a lint
  rule would close that gap.

## Evidence

- `.sstack/game2d-framework/state.md` `### 1-dev User Decisions §3`: "Determinism: runtime guard this iteration; lint rule deferred."
- `### 3-arch §F`: "F. Determinism strategy (AC-4) — pick (a) runtime guard via `g.time.now()` / `g.random.rand()` wrappers under `std.game2d.time`".
- `### 7-verify-rerun-2`: AC-4 PASS via runtime guard.

## Suggested fix direction

1. Add `#[deterministic]` attribute parsing to lint rule infrastructure.
2. Walk attributed `App.update` / `App.fixed_update` / `App.draw` bodies and
   diagnose any call into `std.io.time.*`, unseeded `std.random`, or unordered
   `Dict.iter()`.
3. Emit `GAME-DET-LINT-001` with the call site + guidance to use `g.time.now()` etc.
4. Add spec coverage in `test/system/game2d_deterministic_loop_spec.spl` (extending the runtime-guard cases).

## Related

- Runtime side: `src/lib/nogc_sync_mut/game2d/time/det_guard.spl`
- AC-4: `.sstack/game2d-framework/state.md` `### 1-dev` AC-4
