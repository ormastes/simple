# Four unrelated `LayoutBox` types across the layout lanes (2026-08-10)

**Status:** PARTIALLY RESOLVED — name collision removed, spacing record still duplicated
**Severity:** low (no live defect), medium as a defect-hiding surface

## Symptom

The original report counted three. A `/usr/bin/grep` census found **four**
structurally different box records, none shared:

| Type | Module | Shape | Consumers |
|------|--------|-------|-----------|
| `LayoutBox` + `BoxModel` | `src/lib/common/layout/box_model.spl` | struct, recursive `children: [LayoutBox]`, scalar `x/y/width/height`, `BoxKind`; `BoxModel` = 12 spacing edges, **no** width/height | `src/app/ui.browser/backend.spl`, `src/app/ui.browser/event_bridge.spl` |
| `LayoutBox` + `BoxModel` + `EdgeSizes` | `src/lib/common/render_scene/box_types.spl` | class, `BoxModel` = content rect + three `EdgeSizes` | `src/app/ui.browser/renderer.spl` |
| `BeLayoutBox` | `src/lib/gc_async_mut/gpu/browser_engine/layout_box.spl` | class, `BeBoxKind`, DOM-attached (`StyleProps`, `tag_name`, `text_content`), flat edges + single `border_width` | `ui.chromium/engine_merge.spl`, `gc_async_mut/web/simple_browser_page.spl`, `os/compositor/browser_backend.spl`, +6 specs |
| `LayoutBox` + `BoxGeometry` | `src/lib/blink/layout/block_flow.spl` | class, arena/id: `children_ids: [i64]`, `computed_rect: SkRect`; `BoxGeometry` = width/height + 12 edges | 5 blink render-lane specs |

Note the original report named `src/app/ui.browser/renderer.spl` as a consumer
of `common.layout.box_model`. It is not — it consumes the *fourth* variant,
`common.render_scene.box_types`. The real `box_model` consumers are
`backend.spl` and `event_bridge.spl`.

## Decision: rename the containers, merge the spacing record

The four **container** types are genuinely different data structures, not
divergent copies of one:

- `common.layout.box_model.LayoutBox` is a recursive **value tree** — layout is
  produced by returning a new tree from `layout_node`.
- `blink.layout.block_flow` is an **id arena** holding `SkRect`s, because the
  render-lane contract needs `get_box(id)` lookup and skia rects.
- `BeLayoutBox` is **DOM-attached** — it carries `StyleProps`, `tag_name` and
  `text_content` and is meaningless without a `BeDomNode`.
- `render_scene.box_types.LayoutBox` groups edges into `EdgeSizes` and stores a
  content rect rather than a border-box rect.

Unifying them would drag a skia dependency into `common/` (a tier that has
none), an id arena into the ui.browser value-tree lane, and DOM types into
both. Simple also has **no inheritance**, so there is no base-class route.
Forcing a union type would couple four unrelated concerns to buy nothing.

So the containers get the **rename-for-clarity** outcome, and the one part that
*is* true duplication — the twelve spacing edges, field-for-field identical between
`BoxModel` and `BoxGeometry` — is the merge target.

## Done (2026-08-10)

- **Renamed** `blink.layout.block_flow.LayoutBox` → **`BlockFlowBox`** and
  `layout_box_new` → `block_flow_box_new`, across `block_flow.spl` and all ten
  spec files (`test/01_unit/lib/blink/` and the `test/unit/lib/blink/` mirror).
  Zero residue; `block_flow_spec` held **7/7**. Three `LayoutBox` names remain,
  in three different modules — but the blink one, the one most likely to be
  reached for by new render-lane code, can no longer be confused with them.
- **Added** `test/01_unit/lib/common/layout/box_model_spec.spl` (**9/9**).
  `box_model.spl` previously had **zero** spec coverage — that is why the
  divergence could never have been caught. Three of the nine tests are
  cross-lane **parity** tests asserting that `BoxModel` and blink's
  `BoxGeometry` still mean the same thing by the same twelve field names.
  Sabotage-proved: making `BoxModel.uniform` set `border_top` from `margin`
  (a change touching only the common variant) turns the new spec **RED 3/9**
  while `block_flow_spec` stays **GREEN 7/7** — a live demonstration of the
  exact failure mode this bug describes.
- **Documented** the naming rationale and the remaining duplication in the
  `block_flow.spl` header, replacing the old "do not add a fourth" note (which
  was already wrong — there were four).

## Remaining

`BoxGeometry`'s twelve edges are still a copy of `BoxModel`. The merge is to
give `BoxGeometry` a nested `spacing: BoxModel` field and drop the twelve flat
fields.

**Not done here because** it changes the field-read surface
(`geo.margin_top` → `geo.spacing.margin_top`) across five blink specs, and
**four of those five specs are already RED** for an unrelated pre-existing
statics-initialisation failure (`STATICS_FAILED_KEY`, `Results: 1 total, 0
passed, 1 failed` in `hit_test`, `paint_tree_walker`, `form_paint`,
`image_paint`). Editing them would be broad and unverifiable — the change could
not be proved not to break them.

**Unblock condition:** once the blink statics failure is fixed and all five
blink specs are green, nest `BoxModel` inside `BoxGeometry` and re-run all five.
The parity spec added above is the regression net for that change.

`render_scene.box_types` and `browser_engine/layout_box.spl` are owned by other
lanes and were not touched.

**Do not add a fifth spacing record** — nest `common.layout.box_model.BoxModel`.
