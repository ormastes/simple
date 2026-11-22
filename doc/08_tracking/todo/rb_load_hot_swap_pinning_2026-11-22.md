# TODO: RB-LOAD-01..02 loader hot-swap pinning (non-essential, assert-only)

Spec: test/01_unit/compiler/loader/hot_swap_pinning_spec.spl (@tag:in-development, RED by design)
Plan: doc/03_plan/release/1.0.0/robust_boundaries_library_units_sffi_backends_plan_2026-11-15.md section 9.

No hot-swap path exists in `src/compiler` or `src/app` (grep `hot_swap` = 0 hits on
release/1.0.0, 2026-11-22). RB-LOAD-01 (a reloaded unit is pinned to the interface
digest its dependents were built against) and RB-LOAD-02 (a stale digest refuses the
swap instead of loading) need that path first.

Per owner rule (non-essential = assert-only + todo row), no implementation now.
