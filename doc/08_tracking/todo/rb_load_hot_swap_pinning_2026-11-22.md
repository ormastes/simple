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
- Bug: `atomic_i64_new` resolves to the i64-returning `src/lib/nogc_sync_mut/io/debug_stubs.spl`
  twin under interpreter co-compilation even when imported from `std.nogc_sync_mut.atomic`
  (receiver is `i64`, `.load` not found). Workaround: `atomic_i64_try_new`.
