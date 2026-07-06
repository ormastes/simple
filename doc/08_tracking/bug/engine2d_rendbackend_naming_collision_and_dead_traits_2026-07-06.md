# Architecture: RenderBackend trait naming collision and three dead trait designs

- **Date:** 2026-07-06
- **Severity:** MEDIUM (hazard for unification work, drift risk)
- **Area:** src/lib/gc_async_mut/gpu/engine2d/backend.spl, backend_core.spl, backend_adv.spl, backend_session.spl, nogc_async_mut/gpu/engine2d/backend.spl, nogc_sync_mut/gpu/engine2d/backend.spl, common/ui/backend.spl

## Summary

Two different, unrelated traits both named `RenderBackend` exist in the codebase, creating a grepping hazard for any unification effort. Additionally, three dead trait designs sit beside the one live, fully-implemented trait: `RenderBackendCore`, `RenderBackendAdv` (elaborate design docs, zero implementations), `ComputeSession` (declared with a rich contract, zero implementations), and a third textual copy of the entire `RenderBackend` trait in `nogc_async_mut/backend.spl` that will silently drift from the canonical version the moment either side adds a method. A separate, already-filed compatibility bug: `BackendSessionKind` models the same concept differently across runtime families (enum vs. class).

## Evidence

- **(a) Naming collision:** `engine2d/backend.spl:21-44` defines the pixel-level `RenderBackend` trait (22 methods: clear, draw_rect_filled, draw_text, clip/mask, etc.) implementing GPU dispatching. **Separate, same-named trait:** `src/lib/common/ui/backend.spl:22-40` defines a widget-tree abstraction `RenderBackend` (`render(state: UIState)`, `poll_event`, `supports_mouse`, …) implemented by `src/os/compositor/fb_backend.spl` and `browser_backend.spl`. No namespace distinction; both use `impl RenderBackend for ClassName`.

- **RenderBackendCore/RenderBackendAdv (dead):** `backend_core.spl:23` and `backend_adv.spl:23` declare trait pairs with elaborate docstrings (minimal-core + emulation-derived-advanced split, aimed at exactly the shared-interface goal). Confirmed zero implementations in `.spl` sources: grep `-rln "impl RenderBackendCore\|impl RenderBackendAdv"` → zero hits. `mod.spl` imports them for re-export; `backend_emu.spl`'s actual function signatures use the old monolithic `RenderBackend`, not either Core/Adv variant.

- **ComputeSession (dead):** `backend_session.spl:78-95` declares a compute trait contract (`fill/copy/alpha_blend/blit_rect/scroll/load_module/launch_kernel`) meant to unify session lifecycles. Confirmed zero implementations: grep `-rn "impl ComputeSession src"` → zero hits. Dead scaffolding for the exact unification problem the user is solving.

- **Third RenderBackend copy:** `nogc_async_mut/gpu/engine2d/backend.spl` independently redeclares `trait RenderBackend`/`Engine2DExtended`, byte-for-byte matching the method list of `gc_async_mut/backend.spl:21-47`, as a separate nominal type (not a facade re-export). No concrete backend in that directory implements it (only `backend_lane.spl`/queue scaffolding exists). Forward-looking duplicate for a hypothetical "no-GC migration," but it means three textually-copied `RenderBackend` traits already exist, which will silently drift the moment either side adds a method.

- **BackendSessionKind drift (already filed):** `gc_async_mut/backend_session.spl` models as `enum BackendSessionKind { CpuSimd, ... }` while `nogc_sync_mut/backend_session.spl` models the same concept as a `class` with constructor helpers. See `doc/08_tracking/bug/backend_session_kind_cpu_simd_api_drift_2026-06-01.md` (open, triaged 2026-06-11).

## Failure scenario

1. Unification design chooses to rename the pixel-level `RenderBackend` trait for clarity (e.g. to `PixelRenderBackend`)
2. Engineer updates `gc_async_mut/gpu/engine2d/backend.spl:21` and `engine.spl` dispatch to use the new name
3. Misses `nogc_async_mut/gpu/engine2d/backend.spl` because it's a separate file with an identical name
4. Code compiles locally; unification work silently bifurcates and drifts
5. Later method additions appear only in one trait, breaking cross-family code

The naming collision between pixel-level and UI-level `RenderBackend` means any search-and-replace or grep during refactor must manually disambiguate context.

## Fix direction

1. **Rename one of the two `RenderBackend` traits** (suggest UI-level → `UIRenderBackend`, keeping pixel-level as canonical `RenderBackend`)
2. **Consolidate trait definitions:** retire the dead `RenderBackendCore`/`RenderBackendAdv` pair; delete their files or move to `_archive/`
3. **Delete or dedupe the third copy:** `nogc_async_mut/backend.spl` should either be a facade re-export (like `gc_sync_mut`) or removed entirely; do not maintain a separate nominal copy
4. **Delete ComputeSession** or if it represents a future goal, move it to a design document and mark the file as forward-looking/experimental
5. **Resolve BackendSessionKind drift** in the same change: define one canonical `BackendSessionKind` type (enum or class, consistent across all runtime families)

## Verification targets

- Rename applied consistently: `grep -rn "RenderBackend"` disambiguates by context; no stray drift across gc_async_mut/nogc_async_mut/nogc_sync_mut
- Dead traits removed: `src/lib/gc_async_mut/gpu/engine2d/backend_core.spl`, `backend_adv.spl`, `ComputeSession` declarations do not exist or are clearly marked as non-live
- Third trait copy consolidated: only one `RenderBackend` trait definition in each of `gc_async_mut`, `nogc_async_mut`, `nogc_sync_mut` (as facade if needed)
- UI-level trait renamed: `src/lib/common/ui/backend.spl` and implementations in `fb_backend.spl`/`browser_backend.spl` use `UIRenderBackend`
- BackendSessionKind unified: single source-of-truth representation across all runtime families (or explicit adapters at MDSOC boundaries)
