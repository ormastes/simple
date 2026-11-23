# TODO: RB-LOAD-01..02 loader hot-swap — remaining scope after the identity-pin slice

Spec: test/01_unit/compiler/loader/hot_swap_pinning_spec.spl (GREEN 5/5, 2026-11-23)
Design: doc/05_design/compiler/hot_swap/hot_swap_identity_pin_2026-11-23.md
Plan: doc/03_plan/release/1.0.0/robust_boundaries_library_units_sffi_backends_plan_2026-11-15.md section 9.

Done (2026-11-23): `src/compiler/99.loader/hot_swap_pin.spl` — identity-checked swap via
`smf_cached_unit_identity_admit`, refusal on iface/ABI/triple/policy/capability mismatch and
on a missing identity record, lockless CAS commit on the slot generation.

Done (2026-11-23, hs2): generation -> image wiring in `hot_swap_pin.spl` — `hot_swap_slot_load`
(loader entry, identity-admitted generation 0), `HotSwapImage` per generation, per-call reader pins
(`hot_swap_read_begin`/`hot_swap_read_end`), lockless refcount reclaim (`hot_swap_reclaim`: CAS
readers 0 -> RECLAIMED; a pin is CAS c -> c+1 only for c >= 0). Spec:
test/01_unit/compiler/loader/hot_swap_image_spec.spl (4/4).

Done (2026-11-23, hs3): fixed-capacity generation table, so there is no reader scan and no reallocation race. Pinned entries are never reused. The OS-thread stress
spec is blocked by doc/08_tracking/bug/seed_thread_shared_class_object_crash_2026-11-23.md.

Remaining:
- DONE 2026-11-23 hs4: compat `ModuleLoader.reload_with_intent` admits pinned paths through the slot before unload
  (`moduleloader_pin_hot_swap`, `moduleloader_hot_swap_read_begin`; spec `hot_swap_loader_wiring_spec` 3/3).
- `LazyModuleLoader.moduleloader_replace_live` (99.loader/loader/module_loader.spl) has no slot yet; callers that
  pin modules (startup load policy) do not call `moduleloader_pin_hot_swap` yet; a failed load AFTER an
  admitted swap leaves the slot one generation ahead of the (absent) module.
- State migration across an ABI change (currently refused).
- Land the OS-thread pin/reclaim stress spec once the seed shared-object crash is fixed (or on a native binary).
- Bug (FIXED-VERIFICATION-PENDING 2026-11-23, work/at1-20261123): `atomic_i64_new` resolved to an
  i64-returning stub in `io/debug_stubs.spl`, re-exported by `std.nogc_sync_mut.io`, which shadowed
  the `std.nogc_sync_mut.atomic` import under co-compilation. e1b7d525592 renamed the stubs to
  `debug_stub_atomic_*`; since they had zero callers, they and their re-exports are now deleted
  from all io debug_stubs twins. Guard: `test/01_unit/lib/atomic_import_shadow_spec.spl`.
  `hot_swap_pin` keeps `atomic_i64_try_new` on purpose: it is the non-panicking API for the Err path.
