# Incremental web layout visits NO island — `visited_island_ids` is empty where the spec expects the dirty island

**Date:** 2026-08-01
**Status:** OPEN
**Severity:** MEDIUM-HIGH — incremental layout reports that it touched nothing
while a full pass on the same snapshot + frontier reports two islands. Any
consumer trusting the receipt's `visited_island_ids` sees an incremental pass as
a no-op.
**Found by:** parse-blocker lane, on the FIRST-EVER run of this spec. The spec
could not compile before (see
`stale_seed_binary_blocks_gpu_web_layout_specs_2026-08-01.md`), so this
assertion had never been evaluated.

## Symptom

`test/01_unit/lib/gpu_web/layout/web_layout_incremental_oracle_spec.spl`,
example "visits only the invalidated island on an incremental pass" (line 176):

```
✗ visits only the invalidated island on an incremental pass
  expected [] to equal [3]
```

9 examples, 1 failure. The other 8 pass, including
`visited_island_ids == [1, 3]` for the FULL pass on the SAME snapshot and the
SAME frontier (line 181, passes) and `receipt.mode == "incremental"`.

So the difference is isolated to island SELECTION on the incremental path, not
to the snapshot, the frontier, or the receipt plumbing.

## Repro

```
# from a tree at 3c4caeaf984, with a compiler built at or after 023a60a05aa
bin/simple test/01_unit/lib/gpu_web/layout/web_layout_incremental_oracle_spec.spl
```

Binary used: `bin/release/x86_64-unknown-linux-gnu/simple.pre-segv-fix-20260731`
(Jul 30 build; the deployed `bin/simple_seed` cannot compile the module at all).

## Where to look

- `src/lib/gc_async_mut/gpu/browser_engine/gpu_web/layout/manager.spl:162`
  `web_layout_run_incremental` — differs from `web_layout_run_full` only in the
  `incremental: bool` flag passed to `_web_layout_run`.
- `src/lib/common/structural/layout/engine.spl:636` and `:654` — both
  `StageReceipt.visited_island_ids` and `LayoutSnapshot.visited_island_ids` are
  set from the same `selected_ids`. `selected_ids` is empty on the incremental
  path, so the defect is upstream in dirty-island selection, not in the
  receipt/snapshot wiring.

## Not yet determined

Whether the spec's expectation (`[3]`) or the selector is wrong. Both readings
are consistent with the passing "leaves the frontier empty when nothing
layout-affecting changed" example, which asserts `visited_island_ids == []` for
a paint-only change — i.e. the selector CAN return empty legitimately, and it
appears to be returning empty for a layout-affecting change too.
