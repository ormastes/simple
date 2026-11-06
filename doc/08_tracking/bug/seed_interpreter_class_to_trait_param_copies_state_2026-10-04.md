# Seed interpreter: class passed as a trait-typed argument is copied; `it`-block global assignment lost (2026-10-04)

**Status:** FIXED (already, verified 2026-11-06) — see "Resolution". Was worked around. **Where:** Rust seed `simple test` (interpreter),
release/1.0 seed built at `9731374b4f2`.

## Observed

Writing `test/01_unit/os/drivers/storage/dw_mshc_sd_model_spec.spl`:

1. A `class SdCardModel` (fields: register array, command log, ...) implementing
   `trait DwMshcRegs` was passed to `DwMshcSd.open(regs: DwMshcRegs, ...)`. The
   driver drove the model correctly (the SD state machine advanced, so the
   driver's own copy mutated), but the spec's `card` variable afterwards still
   had an empty command log: the class instance was COPIED into the
   trait-typed parameter instead of shared. Classes are documented as
   reference types, so mutations through the trait object should be visible
   to the caller.
2. Inside an `it` block, `_m_inject_dcrc = true` (a module-level `var` of the
   spec file) had no effect on code reading `_m_inject_dcrc` in a module
   function; calling a module function that performs the same assignment
   worked.

## Workaround

The model keeps all state in module-level globals behind a field-less
`SdModelPort` class, and the spec mutates globals only through module
functions (`sd_model_reset`, `sd_model_inject_dcrc`).

## Next step

Minimal repro: `class C: n: i64`, `trait T: fn bump()`, `impl T for C` with
`me fn bump(): self.n = self.n + 1`, `fn f(t: T): t.bump()`; check `c.n` after
`f(c)` in the interpreter and in a native build.

## Resolution (verified 2026-11-06)

No longer reproduces on a seed built from `release/1.0.0` @ `ecb705896a4` (debug).

- `test/fixtures/seed_interp/class_to_trait_param_shares_state_repro.spl`
  (`run`, interpreter): `trait_param 2` — two `me fn bump()` calls through
  a trait-typed parameter are visible on the caller's instance.
- `test/fixtures/seed_interp/class_to_trait_param_test_lane_repro.spl`
  (`simple test`): 3/3 passed — state shared through a trait-typed param
  (field and pushed log), through a driver that stores the trait object
  from a static `open` and mutates it later, and an `it`-block assignment
  to a module `var` is seen by a module function.

Classes are `Value::ClassInstance` (shared reference storage) by default.
The dw_mshc model's global-state workaround can be reverted at leisure.
No code change in this pass.
