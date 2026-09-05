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

## Merge DONE (2026-08-10)

`BoxGeometry` no longer declares its own twelve edges. It now nests
`common.layout.box_model.BoxModel` as `spacing`, keeping only `width`/`height`
of its own (BoxModel deliberately carries no dimensions). The duplication is
gone: there is now ONE edge declaration reached by both lanes.

**Field identity re-verified before the change** (not inherited from this doc):
all twelve names, order and `f64` types matched exactly.

**Why the old blocker no longer applied.** The doc said four of five blink specs
were RED on a statics failure. The real reason is `reason=unresolved-module` —
they import `std.blink.{dom.form_state,input.event,paint.paint_tree_walker}`,
which do not exist anywhere (see
`blink_specs_import_unimplemented_modules_2026-08-10.md`). They never execute a
test, so they cannot regress. They also only touch `box_geometry_new` /
`box_geometry_zero`, whose signatures are unchanged, so they needed no edit.

**Verdicts (foreground, relative paths, Rust bootstrap seed `bin/simple`):**

| spec | before | after |
|---|---|---|
| `test/01_unit/lib/common/layout/box_model_spec.spl` | 9/9 | **9/9** |
| `test/01_unit/lib/blink/block_flow_spec.spl` | 7/7 | **7/7** |
| `test/01_unit/lib/blink/hit_test_spec.spl` | `reason=unresolved-module` | **unchanged** |

**Cross-lane sabotage proof — the point of the merge.** Setting `border_top: 7.0`
in `BoxModel.zero()` (a single edit in `common/`, touching no blink file) now
turns **both** lanes RED:

- `box_model_spec` 9/9 -> **7/9**
- `block_flow_spec` 7/7 -> **6/7**

Before the merge, this exact class of sabotage turned `box_model_spec` RED while
`block_flow_spec` stayed **GREEN 7/7**. The blink lane now feels a `common/`
change — that is the duplication actually being gone, not merely renamed.
`box_model.spl` was restored and verified byte-identical to HEAD afterwards.

**Language check before committing to the nesting.** Nested struct writes were
probed, not assumed: `o.inner.a = 99.0` persists. A control probe showed struct
assignment on this engine aliases for *flat* structs too (`var f2 = f; f2.a = 7`
mutates `f`), so nesting is no worse than what BoxGeometry already had. Note
this contradicts the "structs are value types, assignment copies" premise —
recorded here as an observation, not fixed (pre-existing, out of scope).

**Fail-open observed:** reading a field that no longer exists (`geo.margin_top`
after the merge) did not raise a compile error — the specs ran and silently
returned wrong values (9->6, 7->5). Field-existence is not checked on this lane;
only the assertions caught it. Worth a separate bug.

## Remaining

`render_scene.box_types` and `browser_engine/layout_box.spl` are owned by other
lanes and were not touched.

**Do not add a fifth spacing record** — nest `common.layout.box_model.BoxModel`.
