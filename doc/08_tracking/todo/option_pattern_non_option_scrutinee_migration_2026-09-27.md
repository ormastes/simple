# TODO — staged migration: reject Option patterns on non-Option scrutinees

- **Date:** 2026-09-27
- **Status:** OPEN
- **Area:** type checking (seed `hir/lower/option_pattern_shape_diag.rs` + pure-Simple type checker)
- **Plan:** `doc/03_plan/compiler/type_system/option_pattern_non_option_scrutinee_migration_2026-09-27.md`
- **Bug:** `doc/08_tracking/bug/option_pattern_accepted_on_non_option_scrutinee_2026-07-27.md`
- **Acceptance spec:** `test/01_unit/compiler/interpreter/option_on_non_option_scrutinee_class_spec.spl`
  (`@tag:in-development` until stage 3)

## Steps
1. Stage 0: measure the real offender set with `SIMPLE_DIAG_OPTION_PATTERN_SHAPE=1`
   across the full build and test tree (the ~2,746 figure counts all Option-shaped
   sites, not offenders).
2. Stage 1: freeze a baseline and add a ratchet gate so new code errors, with
   stale-entry detection and registration in `must_check_gates.sdn`. Mirror the
   check in the pure-Simple type checker.
3. Stage 2: convert existing sites in per-layer batches, shrinking the baseline
   in each PR.
4. Stage 3: make the check a hard error everywhere, then remove the spec's
   `@tag:in-development`.
