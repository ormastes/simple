# TODO: RB-LOAD-01..02 loader hot-swap — remaining scope after the identity-pin slice

Spec: test/01_unit/compiler/loader/hot_swap_pinning_spec.spl (GREEN 5/5, 2026-11-23)
Design: doc/05_design/compiler/hot_swap/hot_swap_identity_pin_2026-11-23.md
Plan: doc/03_plan/release/1.0.0/robust_boundaries_library_units_sffi_backends_plan_2026-11-15.md section 9.

Done (2026-11-23): `src/compiler/99.loader/hot_swap_pin.spl` — identity-checked swap via
`smf_cached_unit_identity_admit`, refusal on iface/ABI/triple/policy/capability mismatch and
on a missing identity record, lockless CAS commit on the slot generation.

Remaining:
- Wire `HotSwapSlot` into the production loader (segment mapping, generation -> image
  publication, reclaim through `unload_ownership.spl` once no reader pins an old generation).
- State migration across an ABI change (currently refused).
- Bug (FIXED-VERIFICATION-PENDING 2026-11-23, work/at1-20261123): `atomic_i64_new` resolved to an
  i64-returning stub in `io/debug_stubs.spl`, re-exported by `std.nogc_sync_mut.io`, which shadowed
  the `std.nogc_sync_mut.atomic` import under co-compilation. e1b7d525592 renamed the stubs to
  `debug_stub_atomic_*`; since they had zero callers, they and their re-exports are now deleted
  from all io debug_stubs twins. Guard: `test/01_unit/lib/atomic_import_shadow_spec.spl`.
  `hot_swap_pin` keeps `atomic_i64_try_new` on purpose: it is the non-panicking API for the Err path.
