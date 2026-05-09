# Bug: Compile-Time Lint for `#[deterministic]` Guard (GAME-DET-LINT-001)

**Status:** OPEN -- deferred. Needs `#[deterministic]` attribute parsing in
lint-rule infrastructure. Runtime guard at
`src/lib/nogc_sync_mut/game2d/time/det_guard.spl` already closes the safety
gap at runtime. No focused fix possible without new compiler infra.
**Date:** 2026-04-25
**Deferred by:** bug-sweep-2026-04-26 phase 2 (research)

---

## Symptom

Game2D deterministic-loop mode requires that tick/render callbacks never call
non-deterministic APIs (wall-clock, random without seed, network I/O). A
`#[deterministic]` annotation on the loop body should produce a compile-time
lint error if such calls are reachable. Currently the guard is runtime-only
(`det_guard.spl` panics on violation), which means the error surfaces only
at execution time.

---

## Why Deferred

1. The compiler does not yet parse `#[deterministic]` as a function attribute.
   Implementing this requires changes to the attribute parsing infrastructure
   in the compiler frontend -- broader work than this iteration.
2. The runtime guard (`det_guard.spl`) already catches violations at execution
   time, satisfying the safety requirement. The compile-time lint is a
   quality-of-life improvement, not a correctness gap.
3. No focused (5-file) diff can deliver this without the compiler infra work.

---

## Required Fix (when unblocked)

1. Add `#[deterministic]` to the compiler's attribute parser.
2. Implement a lint rule that walks the call graph from annotated functions
   and flags reachable calls to non-deterministic APIs.
3. Add reproducer spec under `test/unit/compiler/` or `test/system/`.

---

## Adjacency Audit

No adjacent patterns identified -- this is a new feature request, not a
regression in existing behavior. The runtime guard covers the same semantic
contract.
