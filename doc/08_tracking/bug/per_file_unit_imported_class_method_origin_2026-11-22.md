# Per-file unit lane: method call on an imported class has no proven origin

- Status: fix-implemented in source (2026-11-22); NOT proven on a rebuilt compiler
- Severity: P1 (default per-file route, any ordinary import of a class)
- Found: 2026-11-22, bootstrap CLI closure, Stage 2 built from `a685c58a3f0`
- Component: per-file unit import plan (`src/compiler/80.driver/driver_unit_tldr_imports_v1.spl`)
- Related: `per_file_unit_class_import_cycle_2026-11-21.md` (same failure, treated
  there as cycle-only)

## Symptom

Unit `3/4@0~h0`, target `compiler.frontend.core.collection_feedback`
(`use std.nogc_sync_mut.src.collections.hashmap.{HashMap}`, no cycle):

```
[unit-tldr] import interface-hir miss reason=no-sidecar path=.../src/lib/nogc_sync_mut/src/collections/hashmap.spl
error: E-BACKEND-LLVM-CALL-ORIGIN: lib.nogc_sync_mut.src.collections.hashmap.HashMap.new: callee lacks proven source/runtime/foreign origin
error: LLVM Call destination %l19 was not emitted
```

75 origin errors, all in this one module, for `HashMap.new`, `.with_capacity`,
`.insert`, `.insert_if_absent`, `.get`.

## Root cause

1. The provider was never scheduled before its importer. The order is
   deps-first and the edge is known (the `unit_order.idx` row of
   `collection_feedback.spl` lists `hashmap.spl`), but worker slot `k` of `N`
   starts its scan at `k * limit / N`
   (`_worker_unit_pick_cursor_read_slot_v1`,
   `driver_worker_surface_closure_v1.spl:629`). Slot 3 of 4 took eight
   `10.frontend/core` files as its first pick; `hashmap.spl` sits in slot 0's
   range and had no `.pick`, `.claim` or `.hirkey` when the build stopped (56
   of 2157 rows picked).
2. The wait cannot cover that. `hashmap.spl` is in the frozen inventory, so
   `hir_shard_provider_settle_wait_v1` (`driver_hir_cache.spl:1772`) waits for
   it, but the budget is one 60 s total per unit
   (`driver_hir_pipeline_lowering.spl:1210`) and a unit here runs for minutes.
   The unit logged 361 `no-sidecar` misses against 21 hits.
3. On a miss the import stays a TLDR summary surface. Such a surface gives MIR
   free-function origins only: `register_surface_callable_origins_v1`
   (`provider_metadata.spl:262`) skips methods and statics, and no class or
   struct layout is registered. So every method call on the class is
   `MirCallOrigin.Unknown`, and a construction fails
   `missing exact struct construction layout`.

A re-export or alias path is not involved: `std.` and `lib.` name the same
inventory row and the edge resolved.

## Fix

`unit_tldr_plan_v1` now treats a summary whose surface declares a class, a
struct or methods (`composite_values` or `impls` non-empty) as a fallback
unless the provider's `.hirkey` sidecar already exists in the unit's HIR queue
(or the module is one of the unit's own parse paths). The module's source is
parsed, the existing `[tldr-fallback]` route, logged with
`reason=class-without-interface-hir`. A provider that has published keeps the
summary and is held as interface HIR, as before. `E-BACKEND-LLVM-CALL-ORIGIN`
is unchanged.

Registering method origins from the surface was not chosen: it would not give
the class layout, and the call would still use the fallback link name, which
is not proven to match the provider's definition (see the entry-module finding
below).

Cost: until providers publish, a unit parses and lowers the class-bearing
modules of its import closure instead of summarising them. Not measured at
closure scale.

## Verified (frozen Stage 2, 3-file fixture, serial pool, `MemoryMax=3G`)

`a.spl` declares `class MoxBox` with `static fn make` and `fn doubled`;
`b.spl` imports it and calls both; `main.spl` calls `b`. A watcher deletes each
`.hirkey` as it appears, which is the state the importer met above.
`SIMPLE_FILE_WORKER_BATCH=1 SIMPLE_UNIT_IMPORT_IFACE_WAIT_MS=0`:

| run | result |
|---|---|
| sidecars kept | builds, exit code 42 |
| sidecars removed | `unproven-call-origin: callee=mox.a.MoxBox.make`, `callee=mox.a.MoxBox.doubled` |
| sidecars removed, `SIMPLE_UNIT_TLDR_IMPORTS=0` | builds, exit code 42 |
| `a.spl` forced onto the source fallback (a `pub(package)` row), `b.spl` sidecar kept | builds, exit code 42 |
| struct provider, construction + field read, sidecars removed | `missing exact struct construction layout 'MoxPt'` |

The fourth row is the route the fix takes. The new `if val` block, copied into
a standalone file, compiles on the frozen Stage 2 and returns the expected
value for the three cases (class without HIR, class with HIR, no class).

## Not verified

- The change needs a Stage 2 rebuild; it has not run in a compiler. The spec
  case in `unit_lane_tldr_imports_spec.spl` was not run (no full CLI here).
- A two-worker pool was not reproduced: under `MemoryMax=3G` the pool admits
  one worker, so the importer-first order was emulated by removing sidecars.
- Enum-only and trait-only providers still take the summary. Whether MIR needs
  more than the summary for them was not tested.
- Closure-scale cost and the remaining failures of the bootstrap closure.

## Also seen, not fixed

With every sidecar removed, the ENTRY module's summary-only import of a free
function fails at link: `ld.lld: error: undefined symbol: mox_c_value`. The
same call from a non-entry module links. The summary route keeps the fallback
link name, and for the entry module that name is the bare one.
