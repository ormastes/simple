# Lib Tiers: nogc_async_mut Is the Default

The Simple stdlib has five tiers under `src/lib/`. As of 2026-06-11
(tier-defaults ADR), they are not peers:

| Tier | Role |
|------|------|
| `nogc_async_mut/` | **Default.** Full stdlib surface; every feature reachable here. |
| `nogc_sync_mut/` | Synchronous-optimized variants (no async machinery on hot paths). |
| `gc_async_mut/` | GC-assisted variants (gpu/torch/ML allocation patterns). |
| `nogc_async_mut_noalloc/` | Baremetal / no-allocation subset. |
| `common/` | Tier-neutral pure functions (no I/O, no allocation policy). |

## Rules

1. **New stdlib features land in `nogc_async_mut` first**, implemented in
   pure Simple (per the Pure Simple First rule).
2. Other tiers receive a copy only as a deliberate optimized or
   specialized variant — never as a feature's only home.
3. If a feature exists only in another tier, that is a gap. Close it with
   a wrapper hub in `nogc_async_mut`:

   ```spl
   # src/lib/nogc_async_mut/<module>.spl
   export use nogc_sync_mut.<module>*
   ```

   Wrapper first, native port second. Plain `use` re-exports nothing
   (E0410) — the `export use` is mandatory.
4. Imports in app/compiler code prefer `std.<module>` (resolver default)
   or `std.nogc_async_mut.<module>` explicitly; reach into
   `nogc_sync_mut`/`gc_async_mut` directly only when you specifically
   want that variant's performance/allocation behavior.

## Current wrapper-only modules (port-second backlog)

From `nogc_sync_mut`: channel, hal, mimalloc_compatibility, net_server,
sfm, simd_crypto, tooling. From `gc_async_mut`: gpu_ops, gpu_sffi,
gpu_types, render_scene, web.

ADR: `doc/04_architecture/lib/runtime_family_tier_defaults.md`.
