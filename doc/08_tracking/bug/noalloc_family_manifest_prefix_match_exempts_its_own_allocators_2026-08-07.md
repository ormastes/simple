# `@noalloc` family manifest declares the noalloc family non-allocating, and prefix matching extends that to its own allocator submodules

**Filed:** 2026-08-07
**Severity:** high — this is the load-bearing check for the baremetal/flight tier
**Status:** OPEN

## Summary

`src/compiler/35.semantics/gc_boundary_check.spl:96` hard-codes the runtime-family
manifest row:

```
family: "nogc_async_mut_noalloc", ..., allocates: false
```

and `:140` matches family rows by **prefix** (`path.starts_with(entry.family)`).

`src/lib/nogc_async_mut_noalloc/__init__.spl` publicly exports allocators from
submodules of that same family:

- `:76` `BumpAllocator, FreeListAllocator, FixedBlockAllocator, MultiPoolAllocator`
- `:77` `heap_init, heap_stats, heap_check`
- `:152` `AllocResult, SharedHeap`
- `:190` `init as mimalloc_init, alloc as mimalloc_alloc, free as mimalloc_free`

Because `nogc_async_mut_noalloc.mimalloc` and `nogc_async_mut_noalloc.memory`
both start with `nogc_async_mut_noalloc`, they inherit `allocates: false`.

**Consequence:** a `@noalloc` function that calls `mimalloc_alloc` or uses
`SharedHeap` can never trip the checker's `FamilyImport` rejection
(`noalloc_checker.spl:146-155`, kind at `:23-27`, emitted `:214`). The check
that exists to prove "no heap" is structurally blind to the family's own heap.

The same file's header states the opposite of the manifest row
(`__init__.spl:1-5, :29-33`): *"No heap allocation, no garbage collector"* and
*"alloc_allowed: false (enforced by BaremetalConfig)"*. The tree contradicts
itself.

## Aggravating factors

- **Not a compile gate.** The only non-self caller of `check_all_noalloc_fns` is
  `src/compiler/90.tools/verify/noalloc_manifest_scan.spl:172`, driven only by
  `scripts/audit/noalloc_manifest_scan.spl:12`, which is referenced by nothing
  in `scripts/check/` or `.github/`. It is an offline audit, not CI.
- **The audit is narrower than the checker.** `DirectAlloc` recognises 5
  hard-coded tags (`noalloc_checker.spl:116-126`: `new`, `array_literal`,
  `dict_literal`, `interpolation`, `string_concat`); the audit detects only
  `new` and `interpolation` and says so at `noalloc_manifest_scan.spl:16-24`.
- **Stale contradicting comment.** `effect_verifier.spl:365-367` claims the
  noalloc checker has "ZERO production call sites"; that is now stale, though
  "not a gate" still holds.
- Manifest/tree mismatch nearby: row `async` (`gc_boundary_check.spl:100`) has no
  `src/lib/async/` directory; `src/lib/pure/` has no row and falls to the unknown
  `rank: -1` default (`:142`).

## Unblock condition

Replace prefix matching with exact or explicitly-enumerated submodule rows, and
split the noalloc family so the allocator submodules carry `allocates: true`.
Regression spec must prove a `@noalloc` fn calling `mimalloc_alloc` was accepted
before the fix and rejected after — an absence assertion alone is fail-open here.

Tracked as WP-11 (first Wave-3 item, blocks the allocation-class work) in
`doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md`.
