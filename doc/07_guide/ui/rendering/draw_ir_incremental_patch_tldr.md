# DrawIR Incremental Patching — TL;DR

Additive companion to `draw_ir_diff.spl` (slice item 7 of
`web_wm_gpu_3d_review_2026-07-20.md` Phase 4): `draw_ir_patch_between()`
emits ops instead of a full re-send; `draw_ir_patch_apply()` replays them,
revision-gated. Diff report JSON stays byte-identical for existing
consumers. Not wired into any live producer/consumer yet (library-only).

```sdn
draw_ir_patch:
  index: DrawIrCommandIndex (component_id -> flat-index, O(1), first-wins on dup)
  ops:   Insert | Remove | UpdateGeometry | UpdateStyle(+color/kind/parent_id) |
         UpdateText | Reorder(byte-identical, index moved only)
  apply: gate composition_id == base_revision, else reject "needs full snapshot"
         -> bijection fill (unchanged keep index; ops write at recorded new_index)
         -> collapses to ONE batch (multi-batch split = out of scope)
  damage_rects: old_bounds(if present) + new_bounds(if present) per changed op
  oracle: draw_ir_patch_commands_equal covers kind/component_id/parent_id/
          geometry/color/text_value/computed_style ONLY -- NOT border_rect/
          content_rect/hit_rect/clip_rect/image_uri/edge/points/glyph_run
```

Limitations recorded, not silent: component_id assumed unique; single-batch
apply; oracle field coverage above. Filed bug (untouched here, additive-only
constraint): `simple test` daemon vs `simple run` diverge on the `text?`
per-property lookup pattern that `draw_ir_diff.spl` still uses;
`draw_ir_patch.spl` avoids it with a raw double-loop compare instead (see
`bug_sspec_daemon_optional_lookup_equality_divergence_2026-07-20.md`).

Full guide: [draw_ir_incremental_patch.md](draw_ir_incremental_patch.md)
