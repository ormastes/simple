# Seed co-compilation produces cross-module TypeId incoherence on fresh multi-family parses

Date: 2026-09-18
Host: Windows 11, Git Bash, x86_64-pc-windows-gnu, seed = Rust nightly build

## Symptom

A from-scratch (frontend-cache-miss) parse of the full tree by the seed
fails ~542 files with cross-module HIR type errors:

```
hir: Type mismatch: expected TypeId(4041), found TypeId(4044)
hir: Type mismatch: expected TypeId(5015), found TypeId(1734)
```

The deltas are not constant (3, -4, -8, and wildly different pairs like
5015 vs 1734), so this is not a single registry shift: separately parsed
modules intern structurally identical types to DIFFERENT TypeIds, and the
HIR typecheck sees both sides.

## Why the frontend cache masks it

The per-module frontend cache (src/compiler/10.frontend/frontend_parse_cache.spl)
restores flat-AST pools verbatim, keyed by the file's own content hash
under a scope that folds the compiler source fingerprint. Cache hits skip
the seed's own parse entirely, so a fully warm cache never exercises the
fresh-parse path — which is why builds with an all-warm cache pass (and
why CI passes: its caches are warm). Any cache miss on a multi-family
module (observed: src/plugins/backend_vhdl/*.spl after the merge) falls
into the broken path and fails the whole stage build.

The seed already warns about the underlying hazard at startup:

  "public function `env_get` has 4 co-compiled definitions with 2 differing
   signatures ... a fallback hit may still dispatch to the wrong one"

— the interpreter co-compiles several runtime-family variants
(gc_async_mut / nogc_sync_mut / nogc_async_mut_noalloc / ...) of the same
modules into one process; their TypeId arenas are not unified, so a type
resolved through one variant's registry does not equal the same type
resolved through another's.

## Reproduce

1. Remove the frontend cache (build/bootstrap/native_cache/*/frontend,
   .simple/storage/build/bootstrap/stage3/*/stage*-native-cache/frontend).
2. Run the stage-2 dynload build (see
   doc/08_tracking/bug/cargo_1100_build_dir_layout_breaks_rust_authority_publish_2026-09-16.md
   for the full working lane invocation).
3. Observe hundreds of hir Type mismatch failures.

## Impact

- The low-memory bootstrap mode cannot simply disable the frontend cache
  (its in-memory retention is the ~10GB growth term): disabling it
  exposes this defect and the build fails.
- Any tree change that invalidates part of the cache risks leaving the
  remaining stale entries incoherent with freshly parsed neighbours.

## Suggested direction

Unify TypeId interning across co-compiled family variants (structural /
content-hash interning, or a single shared arena for the parse phase), or
make the multi-family co-compilation dispatch types through one registry.
Related prior art in-tree: the co-compiled-definition warnings above, and
doc/08_tracking/bug/bootstrap_stage2_empty_mir_bodies_2026-07-05.md.
