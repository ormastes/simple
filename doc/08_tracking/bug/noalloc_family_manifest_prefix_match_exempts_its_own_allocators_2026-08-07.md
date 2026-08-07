# `@noalloc` family manifest declares the noalloc family non-allocating, and prefix matching extends that to its own allocator submodules

**Filed:** 2026-08-07
**Severity:** high — this is the load-bearing check for the baremetal/flight tier
**Status:** FIXED (manifest side, WP-11) — see "Fix" section below for scope and a
new gap found while landing it

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

## Fix (2026-08-07, WP-11)

`src/compiler/35.semantics/gc_boundary_check.spl`:

- `runtime_family_manifest_entry` now matches exact-or-dot-boundary
  (`family_path_matches`: `path == family or path.starts_with(family + ".")`),
  not raw `starts_with`.
- `RUNTIME_FAMILY_MANIFEST` gained two submodule rows, listed before the
  family-level `nogc_async_mut_noalloc` catch-all so they take priority:
  `nogc_async_mut_noalloc.baremetal.allocator` and
  `nogc_async_mut_noalloc.mimalloc`, both `allocates: true, noalloc: true`.
  Scoped per WP-13's pointer-level audit (landed `977a401a05cc`, the
  library-side half of this defect): `baremetal/allocator.spl`
  (BumpAllocator/FreeListAllocator/FixedBlockAllocator/MultiPoolAllocator,
  `heap_init`) and `mimalloc.spl` sub-allocate within a caller-supplied
  `(base, size)` region via `rt_mmio_*`/`rt_ptr_*` — no malloc/mmap/brk/libc —
  but that is still real allocation for `@noalloc` purposes.
  `nogc_async_mut_noalloc.memory` (`SharedHeap`) is deliberately **not**
  marked allocating: `SharedHeap.allocate()` returns a logical
  `BinaryRef{id, offset, len}` computed from counters, never a memory
  address. WP-13's first pass called `memory` "arena-bound" and retracted
  that as an overclaim; marking it allocating here would have reintroduced a
  false positive exactly as damaging as the false negative this bug fixes.
  There is no way to express "bounded/static-region sub-allocation" as
  distinct from "heap allocation" in this manifest today — both collapse to
  `allocates: true`; that distinction is deferred to WP-12's five-class
  lattice.
- `GC_ALIAS_MANIFEST` gained a `pure → gc_async_mut` row:
  `src/lib/pure/{tensor,tensor_ops,autograd,training}.spl` are pure
  forwarding facades (`export use std.gc_async_mut.pure.*`, added 2026-07-25
  to stop `std.pure.*` shadowing the real implementation), so `std.pure` was
  never a standalone family and now resolves through the same alias
  mechanism as the existing `gpu` row instead of falling to `rank: -1`.
- The `async` row is confirmed dead (no `src/lib/async/` directory, nothing
  imports a bare `async.*` path; the submodule `nogc_async_mut_noalloc.async`
  is caught by the family-level row above it and never reaches this row) and
  is now documented in place as reserved rather than silently left.

Regression proof (`test/01_unit/compiler/semantics/noalloc_family_manifest_regression_spec.spl`,
driving the real `compiler.semantics.noalloc_checker` module, not a replica):
BEFORE the fix, `Results: 4 total, 2 passed, 2 failed` — a `@noalloc` fn
calling `mimalloc_alloc` or `heap_init` (via `baremetal.allocator`) was
silently ACCEPTED (0 violations). AFTER the fix, `Results: 4 total, 4 passed,
0 failed` — both are REJECTED with `NoallocViolationKind.FamilyImport`, while
a call into the genuinely non-allocating `memory` submodule and other clean
noalloc submodules (`string`, `hash`) still correctly pass with 0 violations.
`test/01_unit/compiler/semantics/gc_boundary_check_spec.spl` (17/17) and
`test/01_unit/compiler/semantics/noalloc_checker_spec.spl` (43/43, untouched
local-replica spec, unaffected by design) both stay green. `bin/simple lint`
on all three changed/added files: 0 errors.

### New gap found while landing this fix — not fixed here, scope is manifest-only

`src/compiler/90.tools/verify/noalloc_manifest_scan.spl:159` — the ONE real
driver of `check_all_noalloc_fns` in the tree — always registers scanned
`@noalloc` functions with `family_module: ""` and never registers their
callees at all. That means `FamilyImport` is **structurally unreachable
through this audit driver regardless of the manifest fix above**: the
manifest split makes `mimalloc`/`baremetal.allocator` correctly classify as
allocating, but nothing in the audit path ever looks up a callee's family, so
the audit can never observe it. Ran `bin/simple run
scripts/audit/noalloc_manifest_scan.spl` before and after this fix: both print
`found 0 @noalloc-annotated functions under src/lib/nogc_async_mut_noalloc`,
identically. Separately confirmed (`grep -rl "@noalloc"
src/lib/nogc_async_mut_noalloc/`) that **zero functions in the tree are
currently `@noalloc`-annotated at all**, so this fix has not (yet) surfaced
any real violation — there is nothing annotated to check. Extending the
audit driver to derive `family_module` from each callee's source location
(or from its own `use` statements) is a distinct, larger change than "fix the
manifest" and is left as a follow-up, not attempted here.

### Newly surfaced (non-fatal) warning surface from the `pure` alias fix

With `std.pure` now resolving through `GC_ALIAS_MANIFEST` instead of falling
to `rank: -1` (previously skipped entirely by `check_gc_boundary_imports`),
two pre-existing real imports become visible:
`src/lib/nogc_async_mut/ml/async_training.spl:6-9` and
`src/lib/nogc_async_mut/ml/data_pipeline.spl:6` import `std.pure.*` from a
`nogc_async_mut` file, which is a genuine `nogc_async_mut` → `gc_async_mut`
crossing. `check_gc_boundary_imports` only emits a warning (this pass is
warnings-not-errors by design, per its own file header), so this is not a
build break, but it is a real, previously-invisible finding worth a look —
not addressed here, out of scope for the manifest fix.
