# ADR: nogc_async_mut Is the Default Lib Set

Date: 2026-06-11
Status: Accepted (user directive)
Related: `runtime_family_stdlib_surface.md`, `host_io_layering/`

## Decision

`src/lib/nogc_async_mut/` is the **default** standard-library tier. Every
feature the stdlib offers must be reachable through
`std.nogc_async_mut.*` (and through `std.*` when the resolver falls through
to it). The other tiers are not peers; they are:

- `nogc_sync_mut/` — synchronous-optimized implementations (no async
  machinery on the hot path). The default tier may delegate here today;
  long-term the dependency direction inverts: sync wraps or specializes
  the default.
- `gc_async_mut/` — GC-assisted variants (gpu/torch/ML workloads where
  arena/GC allocation wins).
- `nogc_async_mut_noalloc/` — baremetal/no-allocation subset.
- `common/` — pure functions shared by all tiers (no I/O, no allocation
  policy); stays tier-neutral.

## Rule for new code

1. New stdlib features land in `nogc_async_mut` first, in pure Simple.
2. Another tier gets a copy ONLY as a deliberate optimized/specialized
   variant (sync fast path, GC arena variant, noalloc subset) — never as
   the only home of a feature.
3. A feature that exists only in another tier is a gap; close it with a
   `export use <tier>.<module>*` wrapper in `nogc_async_mut` until a
   native implementation lands (wrapper first, port second).

## Gap closure (2026-06-11)

Surface audit found 12 top-level modules missing from `nogc_async_mut`;
all now have wrapper hubs (commit pending):

- from `nogc_sync_mut`: `channel`, `hal`, `mimalloc_compatibility`,
  `net_server`, `sfm`, `simd_crypto`, `tooling`
- from `gc_async_mut`: `gpu_ops`, `gpu_sffi`, `gpu_types`,
  `render_scene`, `web`

Wrapper form (matches the repo shim convention, E0410-safe):

```spl
export use nogc_sync_mut.channel*
```

## Follow-up (port-second phase, not yet scheduled)

- Port wrapper-only modules to native `nogc_async_mut` implementations in
  pure Simple, demoting the tier originals to optimized variants.
- Audit sub-module-level gaps (this ADR covers top-level only).
- Teach `bin/simple deps` to flag features reachable only through a
  non-default tier.
