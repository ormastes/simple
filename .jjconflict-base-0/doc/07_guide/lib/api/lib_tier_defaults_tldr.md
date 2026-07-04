# Lib Tier Defaults — TL;DR

- `nogc_async_mut` = the default stdlib tier; full feature surface lives there.
- Other tiers = deliberate optimized variants only (sync fast path, GC arena,
  noalloc subset); `common` = tier-neutral pure functions.
- Feature only in another tier = gap → add
  `export use <tier>.<module>*` wrapper in `nogc_async_mut` (wrapper first,
  pure-Simple port second). Plain `use` re-exports nothing.
- 12 wrappers added 2026-06-11 (channel, hal, net_server, sfm, simd_crypto,
  tooling, mimalloc_compatibility, gpu_ops/sffi/types, render_scene, web).
- Full guide: `lib_tier_defaults.md`; ADR:
  `doc/04_architecture/lib/runtime_family_tier_defaults.md`.
