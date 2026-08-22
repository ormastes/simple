# Glob expansion superlinear in the import closure: the re-export root memo was deleted

**Date:** 2026-08-21 (filed), fixed 2026-08-22
**Area:** `src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl`
**Status:** FIXED (REXMEMO) — pinned by
`test/01_unit/compiler/hir/reexport_physical_cache_spec.spl` (mirrored in `test/unit/`)

## Symptom

Same deployed seed, same module (`compiler.driver.driver`), same 6 glob roots /
73 expansions, FEWER registered imports (9,435 -> 8,284):

| tree | glob sub-phase | HIR total |
|---|---|---|
| `5020e8f3f45` | 69,223 ms | 161 s |
| `d1fd6255ecd` | 194,639 ms | 427 s |

2.8x for the same expansion count means the per-expansion cost grew with the
closure, not a constant factor (`doc/08_tracking/bug/hir_phase_per_module_cost_2026-08-21.md`,
fourth session).

## Root cause

`d757f7d70d0` ("fix(hir): freeze import item projections") deleted the root
re-export memo (`reexport_root_surface_indices` / `_wanted` / `_found` /
`_terminal_indices` / `_items`) from `find_reexport_source` outright, with the
note that "cross-module memo arrays can change meaning after a native module
scope transition". The correctness half of that commit (projecting
`import_item_*` at freeze time instead of from the owner) stands; the memo
deletion was collateral.

Without the memo every `find_reexport_source(facade, wanted)` re-runs
`find_reexport_source_walk`, which for a MISS visits the facade's entire
reachable import graph (depth-capped at 8, cycle-guarded per walk). A glob
expansion calls it once per name the facade does not declare itself, and every
importer in the closure asks the same (facade, wanted) pairs again. Cost per
expansion is therefore O(names x reachable closure), and the reachable closure
grows with the tree — exactly the superlinear term measured.

## Fix (REXMEMO)

`find_reexport_source` now keeps a Dict memo, `"{physical facade index}
{wanted}"` -> terminal surface index (`-1` = complete, valid MISS) plus the
terminal item name (`reexport_root_memo_index` / `reexport_root_memo_item` on
`HirLowering`). What the old arrays got wrong is avoided structurally:

- The answer depends only on the frozen registry, so the memo is keyed on the
  PHYSICAL index (aliases share a row), survives `begin_module`, and is dropped
  whenever `module_surfaces.generation` changes — the same generation check the
  function already used for `reexport_registry_valid`.
- Only a found result or a COMPLETE, VALID miss is recorded; a depth-truncated
  or misaligned walk stays retryable (the existing spec example "does not cache
  a depth-truncated miss" still holds).
- No 512-row cap and no linear `hir_reexport_parallel_find` scan: a Dict probe
  is O(1). The cap existed to bound the array scan, not for correctness.
- Walk state stays on the explicit `HirReexportWalkState` carrier introduced by
  the deleting commit; the memo holds only scalars (an index and a name), never
  a native-heap array, so the "scope transition" concern does not apply.

## Evidence

Mechanism counter, not wall clock: `reexport_chase_memo_hits` on the lowerer.
`test/01_unit/compiler/hir/reexport_physical_cache_spec.spl` (which had gone
stale against the 2-arg `find_reexport_source(facade_index, wanted)` signature
and the freeze-time projection contract, and was failing 15/16 before this
work) is repaired and extended:

| example | pre-fix | post-fix |
|---|---|---|
| shares a positive result across aliases without another walk | FAIL | pass |
| preserves warmed hit and miss roots across begin_module | FAIL | pass |
| rejects a facade index outside the current registry (memo stays empty) | FAIL | pass |
| keeps one memo row per (physical facade, wanted), O(1) probe, dropped on generation change | FAIL | pass |
| 12 behavioural examples (routes, cycles, depth cap, alignment, freeze) | pass | pass |

Wall-clock re-measure on the 662-module closure is owed after the next seed
deploy, as for the other HIR fixes in this series: `[hir-prof]` numbers come
from the compiler doing the work, so a change under `src/compiler/**` only shows
once a compiler built from the patched tree runs.
