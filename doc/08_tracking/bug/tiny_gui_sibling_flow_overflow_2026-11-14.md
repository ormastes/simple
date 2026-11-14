# Tiny GUI sibling flow overflows before coordinate resolution

Status: source fix implemented; review and landing pending. Runtime verification
is unexecuted under the user's source-review-only instruction.

Source inspection at release revision `f998bc43600f8ae22bb7e7db75bc7edd69ecbcce`
found ordinary i32 accumulation in all four sibling-flow paths in
`src/lib/nogc_sync_mut/tiny/gui/state.spl`: indexed row/column scratch updates
and fallback row/column scans. `add` accepts each nonnegative size independently.
Sizes INT32_MAX, 1, 1 therefore make the third child receive an overflowing
sibling offset before the existing saturating pane-coordinate helpers run.
The content-height accumulator already saturates, so it can disagree with
actual geometry. This is a source-derived reproduction, not an observed native run.

The fix reuses `tiny_add_i32_saturating` for the four sums. The existing indexed
and full-scan selection, child relationships, and allocation behavior are
preserved. Five authored behavioral scenarios cover rows, columns, both routes,
and ordinary spacing; their manual explicitly records missing execution.

Remaining separate finding: public same-length edits to node bounds/parent can
leave the child metadata cache valid by node count alone. This change does not
claim to repair that ownership/invalidation problem or remove caching.

Provider token counts and comparable cohort cost: unavailable; no usage ratio
is inferred. No bug database status or competing session claim was changed.
