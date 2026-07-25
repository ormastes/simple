# DrawIR Incremental Patching

`src/lib/common/ui/draw_ir_patch.spl` (`use common.ui.draw_ir_patch.*`) adds
patch generation/application on top of the existing `draw_ir_diff.spl`
report — a way to move a `DrawIrComposition` from one revision to the next
by sending only the operations that changed, instead of re-sending every
command. It is **additive**: `DrawIrCommand`/`DrawIrDiffReport` semantics
are untouched, and the diff report's JSON output stays byte-identical for
its existing consumers. Landed `4da2a2b4eb9` (spec 12/12).

Governing plan:
`doc/03_plan/ui/unified_2d_engine/web_wm_gpu_3d_review_2026-07-20.md`
(landed `d1d22404912` on `origin/main`). This module is **slice item 7** of that plan's
adopted 10-item slice ("O(N) DrawIR patch generation"), assigned to Phase 4
("incremental DrawIR: id maps, O(N) diff, DrawIrPatch, damage bounds,
persistent executor DrawScene, apply + snapshot recovery"). The plan's own
coordinator constraint for this item is the additive-only rule this guide
documents above verbatim: "id maps + patch generation are additive, the
diff REPORT stays for its current users until patch application is
proven." Item 7 also feeds item 8 (persistent per-window GPU surfaces —
see the host-GPU image-resource-retention guide,
`doc/07_guide/platform/simpleos/host_gpu_image_resource_retention.md`) as
its enabler.

## The shared O(N) id-map

Both `draw_ir_diff.spl` and `draw_ir_patch.spl` build a
`DrawIrCommandIndex` (`draw_ir_build_command_index()` in `draw_ir_diff.spl`)
once per composition: a flat `[DrawIrCommand]` list plus a `component_id ->
flat-index` `Dict`. First occurrence wins on duplicate ids. This turns
by-id lookups (`draw_ir_command_index_find()`) into O(1), so diff and patch
generation are O(N+M) instead of the prior nested linear scan. `component_id`
uniqueness per composition is an assumed invariant everywhere this module
touches ids — `draw_ir_patch_apply()`'s bijection fill relies on it, and
duplicate ids are unsupported.

## Op kinds and patch generation

`draw_ir_patch_between(old_composition, old_rev, new_composition, new_rev)
-> DrawIrPatch` walks the new composition's flat command list once against
the baseline index and emits `DrawIrPatchOp` entries:

| kind | `DRAW_IR_PATCH_OP_*` | fires when |
|---|---|---|
| Insert | `INSERT` (0) | id not present in the baseline |
| Remove | `REMOVE` (1) | id was in the baseline, not in the new list |
| UpdateGeometry | `UPDATE_GEOMETRY` (2) | x/y/width/height changed |
| UpdateStyle | `UPDATE_STYLE` (3) | `computed_style` changed, **or** color/kind/parent_id changed |
| UpdateText | `UPDATE_TEXT` (4) | `text_value` changed |
| Reorder | `REORDER` (5) | content byte-identical but flat index moved |

Per-attribute update ops win whenever content differs, even if the index
also moved — `Reorder` is only emitted when nothing else changed. `misc_changed`
(color/kind/parent_id) is folded into `UPDATE_STYLE` rather than getting its
own op kind: without a carrier, a color-only change — the most common
in-place UI diff (hover/selection/theme) — would detect zero ops, and the
apply-side survivor path would silently keep the stale command. `UPDATE_STYLE`
already always ships the full updated command payload, so it doubles as
that carrier. Each non-Reorder op also accumulates `damage_rects`: old
bounds (if present) + new bounds (if present), used for repaint-region
tracking by callers.

## Applying a patch: revision gating and the bijection fill

`draw_ir_patch_apply(composition, patch) -> DrawIrPatchApplyResult` gates on
`composition.composition_id == patch.base_revision`. On mismatch it returns
`ok: false` with a `"revision mismatch ... needs full snapshot"` reason and
the **original, unmodified** composition — the caller's contract is to fall
back to a full snapshot rather than attempt a partial apply. On success the
result's `composition_id` is stamped with `patch.target_revision`, so a
chain of applies can keep using `composition_id` as the revision counter.
`DrawIrComposition` carries no dedicated revision field of its own —
`base_revision`/`target_revision` are caller-supplied identifiers, and
`composition_id` is the natural choice since `draw_ir_diff.spl`'s report
already uses it for `baseline_id`/`current_id`.

Reconstruction (`_draw_ir_patch_apply_commands`) is a **bijection fill**, not
an LCS/ordering computation: every surviving unchanged command (no op
recorded for its id) keeps its baseline flat index, which equals its target
index precisely because a `Reorder` op would otherwise have been emitted;
every non-Remove op writes its command payload at its recorded `new_index`.
`new_index` is unique per surviving id and was observed directly while
`draw_ir_patch_between` walked the new composition, so no separate ordering
pass is needed.

## Batch scoping (deliberate limitation)

`draw_ir_patch_apply()` collapses the result into a **single batch**,
reusing the base composition's first batch's `schema`/`batch_id`/
`backend_target`/`source`/`embedding`. Splitting the result back across
multiple original batches is explicitly out of scope for this slice — the
round-trip oracle compares flattened commands, not batch containers. This
is documented, not a silent gap.

## Round-trip oracle: what is (and isn't) covered

`draw_ir_patch_commands_equal(a, b)` flattens both compositions via the id
map and compares field-by-field: `kind`, `component_id`, `parent_id`,
`x`/`y`/`width`/`height`, `color`, `text_value`, and `computed_style` (via
the same style-diff helper). **It does not compare** `border_rect`,
`content_rect`, `hit_rect`, `clip_rect`, `image_uri`, `edge`, `points`, or
`glyph_run` — those fields are neither diffed nor patchable in this slice.
The round-trip invariant is sound for the fields it does cover; it makes no
claim of full-command coverage. Extending patchable fields means extending
both the op-detection side (`_draw_ir_patch_build_forward_ops`) and the
oracle (`draw_ir_patch_commands_equal`) together.

## A filed, not-fixed-here bug: optional-lookup equality divergence

`_draw_ir_patch_style_changed()` deliberately avoids the `text?`
(nilable) per-property-lookup-then-`== nil`-compare pattern that
`draw_ir_diff.spl`'s `_draw_ir_style_changed()` uses, because that pattern
diverges between the `simple test` daemon evaluator and `simple run` — a
confirmed defect, filed as
`doc/08_tracking/bug/bug_sspec_daemon_optional_lookup_equality_divergence_2026-07-20.md`,
and left untouched in `draw_ir_diff.spl` per the additive-only constraint on
that file's report semantics. `draw_ir_patch.spl`'s own style comparison
instead uses a raw double-loop membership check with no optional in the
comparison path, verified consistent under both evaluators.

## Not proven

This module has unit-spec coverage (12/12) for id-map diff/patch
generation/apply/round-trip; it has not been wired into any live
DrawIrComposition producer/consumer pair (WM frame executor, host-GPU
transport, etc.) as of this landing. Treat it as a library primitive, not
yet an integrated incremental-render pipeline.
