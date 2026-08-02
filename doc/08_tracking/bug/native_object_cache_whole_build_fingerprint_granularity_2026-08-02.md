# Native object cache invalidates the whole build on scoped compiler changes

- **ID:** `native_object_cache_whole_build_fingerprint_granularity_2026-08-02`
- **Status:** BLOCKED — claimed and audited by `pure_parser_close` on 2026-08-02
- **Severity:** High (Stage 3 rebuild amplification)

## Reproduction and measured result

The reported Stage 3 refresh after scoped compiler edits compiled **727** modules
and reused **0** cached objects. Source tracing reproduces the invalidation
decision deterministically:

1. `native_build_compiler_identity()` incorporates a hash of every
   `src/compiler/**/*.spl` file.
2. `driver_native_build_cache_scope()` embeds that identity in the base scope.
3. `driver_native_sources_fingerprint()` hashes the complete loaded source
   closure, and `compile_to_native` adds it as a `sources-*` sub-scope.
4. Per-object `BuildCache.update_entry` records `dependencies: []`.

Therefore one compiler edit selects a new directory before any of the 727
per-source fingerprints can be considered: 0/727 hits is the designed outcome
of the current key structure.

## Why the apparent one-line fix is unsafe

Dropping the compiler or closure aggregate would reuse an unchanged source's
object even when a changed compiler pass changes its generated code, or when an
imported type/interface changes its layout. The cache has neither a canonical
post-lowering MIR hash nor per-module dependency interface hashes on this path.
The existing empty dependency list cannot prove reuse safe.

## Required safe fix

Use a two-level key:

1. stable backend/target/options plus executable producer ABI identity;
2. per module, a canonical MIR fingerprint and ordered direct-dependency
   interface hashes.

Then a private scoped change should produce 726 hits / 1 miss in the reported
727-module fixture, while a producer transformation or public interface change
must invalidate every actually affected module. Until those fingerprints exist,
the measured safe delta remains **0 additional hits**; preserving correctness
requires the coarse refresh.

This audit does not touch HIR aggregate or module-surface files.

