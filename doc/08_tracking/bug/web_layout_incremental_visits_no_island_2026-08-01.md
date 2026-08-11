# Incremental web layout visits NO island — `visited_island_ids` is empty where the spec expects the dirty island

**Date:** 2026-08-01
**Status:** FIXED 2026-08-01 (see resolution at end) — compiler-level bare-name collision remains OPEN
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

---

## RESOLVED 2026-08-01 — root cause was NOT island selection

**Status:** FIXED. The spec is now 9 examples, 0 failures.

The "Where to look" section above is wrong, and so is the original isolation to
`engine.spl` / `selected_ids`. `selected_ids` is empty because its *input* is
empty: the dirty frontier itself never contains a single node.

### Proved chain

Instrumented probe under the tree-walking interpreter
(`bin/simple test`, which delegates to the Rust seed child), same snapshot and
same frontier as the failing example:

```
dirty_frontier changes.len=1        # the change IS delivered
change_frontier entered             # _web_layout_change_frontier runs
EQ Style no                         # change.kind == WebLayoutMutationKind.Style is FALSE
localmatch=WILDCARD                 # match on change.kind hits NO arm at all
dirty_frontier result.len=0         # frontier is empty
input.invalidated_ids=              # empty
island root=1 dirty_bits=0 nodes=1,2
island root=3 dirty_bits=0 nodes=3,4
inc visited=          full visited=1,3,
```

`_web_layout_change_frontier` (invalidation.spl:98) matches `change.kind`
against four `WebLayoutMutationKind` arms with no wildcard. For a `Style`
change **no arm fires**, so `merged` is returned untouched and the whole
frontier construction is a silent no-op. Every downstream stage then correctly
reports "nothing is dirty".

### Root cause: bare-name collision on the variant name `Style`

The same enum variant has different identities in different modules:

| construction site | match site | result |
|---|---|---|
| spec | spec | matches `Style` |
| invalidation.spl (`val here = WebLayoutMutationKind.Style`) | invalidation.spl | matches `Style` |
| spec | invalidation.spl | matches **NOTHING** (wildcard) |
| spec (`WebLayoutMutationKind.Insert`) | invalidation.spl | matches `Insert` correctly |

`Insert` crosses the module boundary correctly; `Style` does not. A probe that
called `WebLayoutMutationKind.Style.to_text()` produced

```
semantic: unknown static method to_text on class Style
```

i.e. the variant is resolved through a global bare-name registry entry `Style`,
which four other declarations also claim:

- `src/lib/nogc_sync_mut/tui/style.spl:55` — `struct Style`
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_style.spl:7` — `class Style`
- `src/app/llm_caret/claude_full/native_ts/yoga_layout/index.spl:67` — `class Style`
- `src/app/llm_caret/claude_full/native_ts/color_diff/index.spl:52` — `class Style`

PROVED: the collision is on the bare name `Style`, and renaming the variant
fixes it. NOT proved: which of the four declarations wins, or the exact
registry mechanism in the resolver. This is the first *reproduced* instance of
the bare-name-collision family (previously recorded as an unproven theory).

### Fix applied

Renamed the variant `WebLayoutMutationKind.Style` -> `.StyleMutation`
(8 occurrences at 8f79e3e2cbe, all renamed; 0 bare refs remain). No spec
assertion was changed or weakened — only the variant spelling.

This is a workaround at the product layer. **The compiler defect is still
open**: an enum variant whose bare name collides with a class/struct name
elsewhere in the program silently fails to match across a module boundary, with
no error and no warning. A `match` over a non-exhaustive-looking enum that
falls through every arm should at minimum diagnose.

### Verification (tree-walking interpreter lane, seed child)

| spec | before | after |
|---|---|---|
| `test/01_unit/lib/gpu_web/layout/web_layout_incremental_oracle_spec.spl` | 9 examples, 1 failure | **9 examples, 0 failures** |
| `test/01_unit/lib/gpu_web/layout/web_layout_manager_spec.spl` | 4 examples, 0 failures | 4 examples, 0 failures |
| `test/03_system/app/web_browser/feature/web_layout_manager_spec.spl` | 3 examples, 3 failures | 3 examples, 3 failures (pre-existing, unchanged) |
| `test/03_system/app/web_browser/feature/web_layout_manager_wpt_parity_spec.spl` | 3 examples, 3 failures | 3 examples, 3 failures (pre-existing, unchanged) |

Both system specs were confirmed RED at the unmodified origin tip before the
fix, so they are not a regression from this change. They remain open.

Binary: `simple.pre-segv-fix-20260731` (Jul 30, 154 MB), post-`023a60a05aa`.
The deployed `bin/simple_seed` (Jul 25) still cannot parse the module.

### Follow-up: the suite is nearly vacuous on island selection

Sabotage check, as requested: `_layout_dirty_island_ids` in
`src/lib/common/structural/layout/engine.spl` was stubbed to `return []` on a
GREEN tree. Only **one** of the nine examples went RED — the same
"visits only the invalidated island" example.

In particular "produces the same geometry incrementally as a full relayout"
stays GREEN while the incremental pass selects **zero** islands. That oracle
compares boxes/fragments/overflows/output_hash, but the merge path backfills
retained geometry for unselected islands, so it cannot distinguish
"recomputed correctly" from "recomputed nothing". Eight of the nine examples do
not gate island selection at all. Worth strengthening separately — e.g. assert
`receipt.item_count_out` or an island-scoped recompute count, not just merged
geometry.
