# Bug Report: STATIC_MAX_LEVEL compile-time level filter not wired

**Bug ID:** B-LOG-CTL
**Date:** 2026-04-25
**Severity:** P3 - Low (deferred; runtime level filter covers the common case)
**Component:** `src/lib/log.spl` + compiler const-folding
**Status:** Open, deferred from sstack/log-lib-drivers Phase 7

## Summary

Phase 3 §H of `sstack/log-lib-drivers` specified a build-time constant
`STATIC_MAX_LEVEL` so performance-critical paths could compile out
sub-threshold `log_*` calls (parity with Linux `pr_devel`, Zephyr
`LOG_LEVEL_INF`, Rust `tracing::level_filters::STATIC_MAX_LEVEL`).

The Phase 5b/6 implementation in `src/lib/log.spl` ships only the
runtime per-subsystem level filter (`log_set_level`,
`log_set_subsys_level`, `log_init_from_config`). The compile-time
constant is not present.

## Acceptance Criteria Impact

`AC-3` of the log-lib-drivers feature reads:

> A unified log facade lives in `std` with a swappable backend [...];
> compile-time level filter available for performance-critical paths.

The runtime half of AC-3 is satisfied (verified by executable proof in
Phase 7). The compile-time half is deferred.

Marked as PARTIAL (`[~]`) in the Phase 7 final AC table.

## Why Deferred

Wiring `STATIC_MAX_LEVEL` requires compiler support for const-folding
`if STATIC_MAX_LEVEL < TRACE: ...`. Adding that const-fold is a compiler
change, not a stdlib change, so it falls outside the Phase 5/6 stdlib
scope. Expanding scope to land it now would conflict with the Phase 7
"verify only" blinders.

## Plan

1. Either:
   a. Compiler change: const-fold `if CONST_VAL < CONST_VAL: ...` in
      the desugar/HIR layer, then add `val STATIC_MAX_LEVEL: i64 = ...`
      to `src/lib/log.spl` and gate every `log_*` call site.
   b. Macro / `#![cfg(...)]` analog at the parser layer to produce
      no-op call sites at parse time when level < threshold.

2. Add a spec at `test/unit/lib/log_static_max_level_spec.spl` that
   asserts compiled-out callsites do not emit (e.g. by checking ring
   pending count after a sub-threshold `log_trace`).

## Owners / Links

- Architecture spec: `.sstack/log-lib-drivers/state.md` §3-arch §H.
- Reference: `tracing` crate `STATIC_MAX_LEVEL` in
  `src/compiler_rust/vendor/tracing/src/level_filters.rs:66`.
- Phase 7 verify report: `.sstack/log-lib-drivers/state.md` §7-verify.
