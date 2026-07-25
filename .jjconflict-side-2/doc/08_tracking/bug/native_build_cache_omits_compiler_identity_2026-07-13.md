# Native-build cache omits compiler identity

**Status:** Resolved 2026-07-16 — identity-in-key verified empirically
(miss on compiler change proven end-to-end; see Regression evidence). The
companion "same compiler retains hit" leg is blocked by a separate
pre-existing cache-reload defect, filed as
`native_build_cache_entries_lost_on_reload_2026-07-16.md`.

**Reopened + re-resolved 2026-07-16 (interpreted-source facet):** the
executable-sha256 identity was incomplete. When the compiler pipeline runs
LIVE-INTERPRETED from `src/compiler/*.spl` (the normal state of the deployed
seed binary), editing a lowering changes codegen while the executable — and
therefore the cache scope — stays identical, so stale objects keep getting
linked and a compiler fix appears not to work. Reproduced end-to-end:
marker edit in `_MirToLlvm/core_codegen.spl` string-const emission; rebuild
of the same entry (with or without `--clean`) reused the stale object
(old output), while a fresh entry filename showed the new behavior.
Fix: `native_build_compiler_source_fingerprint()` in
`driver_build/incremental.spl` — walks `src/compiler/**/*.spl`, builds a
`path|size|sha256` manifest, hashes it via a temp file
(`rt_hash_text`/`rt_hash_sha256` are unavailable under the seed
interpreter), and folds `+src<digest16>n<count>` into
`native_build_compiler_identity()` (memoized per process; ~90-100 ms for
2933 files; "" i.e. unchanged identity when no `src/compiler` tree is
visible from the build cwd). Verified: compiler-source edit -> new scope
`...+src<fp>` -> miss + correct new output; revert -> miss + original
output; unchanged rebuild -> hit. Additionally `--clean` now actually
wipes the entry's cache scope (CLI sets `SIMPLE_NATIVE_BUILD_CLEAN=1`,
`driver_aot_output.spl` consumes it and `rt_dir_remove_all`s the scope
root), and a cache hit now requires all cached objects to still exist on
disk.

## Symptom

After changing compiler lowering or code generation and bootstrapping a new
compiler, native-build can reuse unchanged module objects emitted by the old
compiler. SimpleOS compiler validation therefore requires an empty target cache
and recompiles all 617 modules (345-634 seconds observed).

## Owner evidence

- `src/compiler/80.driver/driver_build/incremental.spl` scopes and validates
  cache entries from module source/options/output existence, without compiler
  identity.
- `src/compiler/80.driver/driver_aot_output.spl` accepts those hits and records
  module fingerprints with empty dependency metadata.

## Required fix

Include a stable compiler/codegen identity in the cache scope or entry
fingerprint. A newly bootstrapped compiler must invalidate objects produced by
an older compiler, while repeated builds with the same compiler retain hits.

## Regression gate

Build one fixture into a cache, change the compiler identity while leaving the
fixture unchanged, and require a miss; repeat with the same identity and
require a hit.

## Resolution (2026-07-15)

The pure-Simple cache scope includes the running compiler content hash, so a
compiler change invalidates otherwise unchanged module objects while repeated
runs of the same compiler retain the same scope. The focused runtime test was
added but not executed in this source-only audit.

## Regression evidence (2026-07-16)

Key construction (pure-Simple pipeline):

- `src/compiler/80.driver/driver_build/incremental.spl:40`
  `native_build_compiler_identity()` = SHA-256 of the running compiler
  executable (`rt_file_hash_sha256(rt_cli_get_args()[0])`), failing closed to
  a per-process `uncacheable-<pid>-<micros>` token when the hash is
  unavailable.
- `src/compiler/80.driver/driver_build/incremental.spl:49`
  `native_build_cache_scope_key(...)` appends `;compiler=<identity>` to the
  scope string.
- Consumed at `src/compiler/80.driver/driver_aot_output.spl:86`
  (`driver_native_build_cache_scope`, native object cache under
  `build/native_cache/<scope>/object.<module>.o`) and
  `src/compiler/70.backend/build_native.spl:62` (SMF cache).

Empirical run (live-interpreted pipeline, deployed seed binary copied to two
files: `simple_a` pristine, `simple_b` = same binary + 1 appended byte):

1. `simple_a native-build --entry pv.spl -o out --clean` then a re-run created
   scope dir
   `build/native_cache/backend=llvm;cpu=native;features=;opt=3;compiler=561767c6615bc013b546dc98065c0a85aff00c522b8bc427045525c72c8e2d6c`
   — the suffix equals `sha256sum simple_a` exactly.
2. `simple_b native-build --entry pv.spl -o out` (source unchanged, compiler
   changed) reported `[NATIVE] cache: 0 hits, 1 misses`, recompiled, produced
   a correct binary (rc=42), and created a NEW scope dir
   `...;compiler=23d1dff95467bb32fc0a5cdd18aaf0e75340894e18fdc3308218f01c15d7fbec`
   = `sha256sum simple_b`. The old scope's `object.pv.o` mtime was untouched
   — no stale reuse across compiler identities. Regression-gate "miss on
   identity change": PASS.
3. Regression-gate "hit on same identity": NOT demonstrable in the
   live-interpreted harness — `BuildCache` reload loses all entries across
   processes (SDN `entries: [...]` parses back empty + BuildCache dual-class
   dispatch collision), so every cross-process lookup misses regardless of
   identity. That defect predates this fix and is filed separately; the
   in-scope reuse filter (`driver_native_build_filter_scoped_outputs`,
   driver_aot_output.spl) only accepts outputs under the current
   compiler-scoped root, which is the correctness-critical half.

Verified at 6456be19e64 (the commit that introduced the fix; cache-key code
is byte-identical at 8ac25987333). Native-build itself is broken at
8ac25987333 by unrelated WIP commit ca1e18c1744 ("checkpoint memory leveling
native verification": `rt_dict_*` extern migration incompatible with the
deployed 2026-07-11 seed interpreter, bisect-proven), so end-to-end runs were
executed at the fix commit.
