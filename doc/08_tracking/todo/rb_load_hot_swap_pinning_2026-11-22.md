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
- DONE 2026-11-23 hs5: `LazyModuleLoader.moduleloader_replace_live` swaps through the slot at its commit point
  (after candidate map + relocation; refusal unmaps the candidate).
- FIXED-VERIFICATION-PENDING 2026-11-26 (work/rb-load02-hotswap-20261126): the lazy path accepts an
  identity-carrying SMF. The driver writer marks its Code symbol with the explicit section index
  (byte 43 = 0x53), the batch preflight tolerates a read-only Note section (`.simple_meta`; a symbol or
  relocation naming it is still refused), and `moduleloader_apply_relocations` refuses v1.2+ only when a
  Data/RoData/Bss section is present, so `replace_live` can patch a Code + Note image. Spec:
  `hot_swap_identity_accept_spec` 4/4 (mapping-free). End to end (`hot_swap_lazy_wiring_spec`,
  `hot_swap_autopin_spec`) stays `@tag:in-development`: on the Windows seed the exec-mapping twin
  `loader/smf_mmap_native.spl` cannot bind its aliased imports (`owner_alloc_exec_memory` not found,
  `smf_group_batch_load_spec` 6/7 RED on the base too; bug family
  `aliased_import_shadowed_by_local_fn_native_codegen_2026-09-03`).
- DONE 2026-11-23 hs5: a failed load after an admitted swap rolls the slot back (`hot_swap_rollback`, one CAS);
  reclaim runs only after a successful load, and before each swap so a rolled-back entry cannot wedge the slot.
- FIXED-VERIFICATION-PENDING 2026-11-26 (work/rb-load02-hotswap-20261126): the pin is now at the loader
  load API, so no caller cooperation is needed. `moduleloader_load_native_batch_v1` decodes the unit
  identity each image carries and pins it at generation 0 from the mapped bytes (no re-read); every
  later `moduleloader_reload` is admission-checked. Slots are built for the whole batch before any is
  published. A live slot is never replaced: re-pin with the same identity is a no-op, a different one is
  `SMF-E-HOTSWAP-ALREADY-PINNED`, and a batch load of a pinned path is refused. There is still no CLI
  reload command (`simple tooling watch --hot-reload` only prints); the covered caller is
  `grouped_native_worker` (batch load).
- OPEN: `moduleloader_unload` does not retire a path's slot, so a pinned path cannot be batch-loaded again
  after unload (fails closed).
- State migration across an ABI change (currently refused).
- Land the OS-thread pin/reclaim stress spec once the seed shared-object crash is fixed (or on a native binary).
- Bug (FIXED-VERIFICATION-PENDING 2026-11-23, work/at1-20261123): `atomic_i64_new` resolved to an
  i64-returning stub in `io/debug_stubs.spl`, re-exported by `std.nogc_sync_mut.io`, which shadowed
  the `std.nogc_sync_mut.atomic` import under co-compilation. e1b7d525592 renamed the stubs to
  `debug_stub_atomic_*`; since they had zero callers, they and their re-exports are now deleted
  from all io debug_stubs twins. Guard: `test/01_unit/lib/atomic_import_shadow_spec.spl`.
  `hot_swap_pin` keeps `atomic_i64_try_new` on purpose: it is the non-panicking API for the Err path.
