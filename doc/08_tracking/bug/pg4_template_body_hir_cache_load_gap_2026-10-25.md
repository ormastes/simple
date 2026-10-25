# P-G4 gap: the template-body seam cannot load an owner body this child does not already hold

**Status:** open. This is P-G5 scope.
**Filed by:** P-G4 (#4625)

## The gap

`driver_reader_concrete_instance_v1` can only serve an owner HIR that the MIR
child has already admitted, meaning it is non-nil in `ctx.hir_modules`. When
the owner is in F's import closure but its HIR is not loaded in this child,
the request misses with `owner-body-unavailable`, and F then goes through
widen and on to MONO-PENDING.

## Why P-G4 does not close it

An HIR cache entry is keyed by
`hir_cache_key(source_path, closure_digest, is_entry)`, defined in
`driver_hir_cache.spl`. The owner's `closure_digest` comes from that owner's
module-surface closure, and the MIR child does not hold it. Without that
digest the child cannot name the owner's published HIR artifact by content
identity. Guessing the key, or re-deriving it by parsing the owner's closure,
would break the per-file contract.

## What closing it needs

The HIR child should publish each module's HIR cache key, or its closure
digest, in its ledger record. A `.deps` sibling under the HIR queue is one
option. With that in place, the loader can call
`hir_cache_load_in_owned_scope(key)` for owners in F's import closure. These
loads should be single-flight and set-once.

## Second limit

`HirImport.module_path` holds the path as written in the source. If that
spelling differs from the `ctx.hir_modules` key, the closure walk stops at
that edge. That is fail-closed: the result is a miss, never a wrong owner.
