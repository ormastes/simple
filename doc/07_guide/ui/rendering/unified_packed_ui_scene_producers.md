# Unified Packed UI Scene: Writing a `UiPackedProducer`

`src/lib/common/ui/ui_scene_slice.spl`'s `UiPackedProducer` trait
(`count()`/`emit()`) is the one contract WM, GUI, Web and external-surface
producers implement to write disjoint pre-reserved ranges of one physical
DrawIR-v3 arena per session, instead of each front end owning a separate
scene. Landed producers: `ui_gui_packed_producer.spl` (L6, `1e0a4c18b0b`),
`ui_web_packed_producer.spl` (L7, `721bc3f579b`), `wm_packed_producer.spl`
(L8, `ed086bb06d4`). Design authority:
`doc/05_design/ui/unified_packed_ui_scene.md`. Feature-expert handoff notes:
`doc/00_llm_process/feature_expert/unified_packed_ui_scene/skill.md`.

This guide is the practical "how do I write the next one" companion — the
mistakes below each cost a real debugging cycle while landing/following up on
L6-L9, and each now has a regression test in the landed producers' own specs
proving the fix; copy that test pattern for any new producer.

## The `count()`/`emit()` contract in one paragraph

`count(snapshot_id, counts) -> UiSceneCounts` must be pure and repeatable:
report the exact row count this producer needs for every one of the 16
tables, for this snapshot, with no side effects. The caller
(`ui_scene_scan`) then prefix-sums every producer's counts into disjoint
`UiSceneRanges`. `emit(snapshot_id, ranges, draw, owners, actions) ->
UiSceneEmitResult` must write EXACTLY that many rows into the
caller-supplied writers — under- or over-emission both abort the generation
(`UiSceneWriteVerdict.Deficit`/`Surplus`), never a partial/guessed delivery.

## Mistake 1: minted/copied ids must be arena-absolute

Every table-row-index field a command carries (`geometry_id`, `paint_id`,
`text_run_id`, `image_resource_id`, `path_span_id`, `clip_id`,
`transform_id`, `hit_shape_id`), plus `TextRun.glyph_start`,
`PathSpan.point_start`, `Clip.parent_id`, `Provenance.command_index`, and
`UiOwnerRecord.action_binding_id`/`parent_owner_id` when you mint them
yourself, are read back as **absolute indices into the assembled arena's
combined per-table array** — never producer-local. The convention (already
used by `draw_ir_v3_emit_full.spl`) is:

```
val id = ranges.<table>.start + draw.cursor(UI_SCENE_TABLE_<TABLE>)
draw.put_<table>(...)   # write the row AFTER capturing its id
```

If you copy an existing oracle's scene verbatim (as L6/L7 do, adapting
`draw_ir_v2_to_v3`'s output), its ids are numbered **locally to that one
call** — rebase every one of them by the matching `ranges.<table>.start`
before writing, with a `NO_ID`-safe helper:

```simple
fn _rebase_id(id: u32, start: u32) -> u32:
    if id == DRAW_IR_V3_NO_ID: DRAW_IR_V3_NO_ID else: id + start
```

`component_id`/`parent_id` (on commands) and `semantic_id` (on owner
records) are **identities**, matched by value across producers — never
rebase those at the single-producer-write level (but see Mistake 4: when
COMBINING multiple producers' output, these DO need a per-producer offset).

**Why single-producer tests won't catch this**: with only one producer in
the scan, every `ranges.<table>.start == 0`, so a missing rebase is
invisible. L6 and L7 shipped this bug for one landing cycle before a
two-producer regression test (a dummy first producer with non-zero counts,
then asserting the real producer's emitted ids are `>= ranges.<table>.start`)
caught it — see either spec's `describe "... id rebasing under a non-zero
assigned range"` block for the pattern.

## Mistake 2: `commands[0]` of a composed v2 batch is a GROUP wrapper

If your producer adapts an existing v2 `DrawIrComposition` via
`draw_ir_v2_to_v3` (as L6/L7/L8 all do), remember `draw_ir_v2_to_v3.spl`'s
own header doc: **every v2 batch becomes one v3 GROUP command** carrying
that batch's embedding translation/clip/opacity, with the batch's own
commands nested as its children. So `scene.commands[0]` for a single-batch
producer is that GROUP, not the batch's content — and its `paint_id` stays
`NO_ID` whenever the batch's embedding opacity is the default 1000 (no
paint row gets minted for it). If you need to patch something about "the
batch's own visual content" post-composition (L8's background-color patch
does exactly this), walk to the GROUP's child (`commands[i].parent_id ==
commands[0].component_id`) rather than assuming index 0 is paintable.

## Mistake 3: giving every hit_shape row an owner is necessary but NOT sufficient

Design section 2.4 requires one `OWNER_RECORDS` row per `HIT_SHAPES` row
your producer emits. How you DECIDE what's hit-testable differs per front
end — don't assume one strategy covers both:

- **Web**: the v2 oracle already marks ordinary boxes hit-testable (a
  plain 2-div page produced 5 hit_shapes from 6 commands, zero interactive
  tags). Give every existing hit_shape row one owner — no custom detector.
- **GUI**: the widget-tree oracle never sets `hit_rect` for anything.
  Locate interactive widgets yourself (`kind_name()` in
  `button`/`checkbox`/`input`/`textfield`) and add a synthetic hit_shape +
  owner row per one, additive to the oracle's own (empty) output.

But an owner row alone doesn't make a hit_shape REACHABLE.
`draw_ir_v3_group_resolve_hit_test` only ever considers commands whose OWN
`hit_shape_id` is set — it never scans the HIT_SHAPES table directly. A
synthetic hit_shape with no command cross-referencing it back
(`command.hit_shape_id == this row`) can never be hit-tested at all, no
matter how correct its owner record is. L6 shipped exactly this gap for a
full landing cycle: every interactive widget got a hit_shape + owner, but
no command pointed at it, so GUI's buttons/checkboxes/inputs were silently
unroutable. The fix needed a way to find "the real command that draws
THIS widget" from outside `draw_ir_v2_to_v3.spl` without touching its
existing signatures — see `draw_ir_v2_to_v3_command_ids_for(composition,
component_ids: [text]) -> [u32]`, a small additive export that re-runs the
adapter's own deterministic id-assignment pass and looks up each v2 text
`component_id` (a widget's own `rect.id`, or a kind-specific derived key
like checkbox's `"{rect.id}-box"` — see `widget_draw_ir.spl`'s
`_emit_widget`, the FIRST command it pushes per kind) in the resulting
map. `ui_gui_packed_producer.spl` uses the returned numeric id to find and
patch that command's `hit_shape_id`. If you write a new hit-testable
producer, ask: does some REAL command actually carry `hit_shape_id ->
your synthetic row`? If not, it's unreachable regardless of how correct
the owner record looks.

## Nesting: `host_parent_id` and `host_owner_id`

A producer hosted inside another (a WebView inside a GUI window, a GUI
window's content inside a WM window) takes two independent, orthogonal
nesting parameters, both defaulting to `DRAW_IR_V3_NO_ID` for a standalone
render:

- `host_parent_id: u32` — a **command** identity. Root commands
  (`parent_id == NO_ID`) get re-parented onto it, so the visual tree nests
  correctly (`WebPackedProducer`'s `_web_reparent_roots`).
- `host_owner_id: u32` — an **owner** absolute index. Every owner record
  the nested producer emits (typically all flat/root within its own
  scope) gets re-parented onto it, so `ui_scene_event_route.spl`'s
  reverse-routing bubble walk reaches the host, and the host's host, and
  so on up to WM.

The host doesn't know its own absolute owner index until it has actually
`emit()`'d (the writer assigns it at write time) — so composing N nested
producers is always **staged**: emit the outermost host first, scan its
`owners.records_snapshot()` for the specific row you need (never
arithmetic-guess the write order), compute
`ranges.owner_records.start + <local index found>`, and pass that as the
next producer's `host_owner_id` before emitting it. See
`test/02_integration/ui/unified_packed_scene_nesting_spec.spl` for a full
worked WM→GUI→Web example, including `wm_packed_producer.spl`'s
`wm_packed_producer_window_owner_semantic_id` — the deterministic query a
caller uses to find which owner record represents a given window.

## Mistake 4: combining multiple producers' output needs id offsetting

Each producer's own oracle independently starts its own `component_id`
counter at 0. If you naively concatenate multiple producers' commands
(as any real multi-producer assembler eventually must — none exists yet;
the integration spec above does this inline), their `component_id`s
collide, breaking `draw_ir_v3_group_resolve`'s structural parent-child
matching entirely (`ok=false, states=[]`). Rebase each producer's
`component_id`/`parent_id` (on commands and hit_shapes) and the matching
owner `semantic_id` by a per-producer offset before combining — offset =
running total of commands already appended, not a magic constant
(collision-free by construction).

## Mistake 5: owner `semantic_generation` must equal the real command's `component_generation`

`ui_scene_event_route.spl`'s "recycled slot" check is an EQUALITY
comparison between the hit command's own `component_generation` and the
owner's `semantic_generation` — not a non-zero check. `draw_ir_v2_to_v3`
sets `component_generation: 0u32` unconditionally on every command it
emits, so any owner backed by an oracle-copied (or oracle-derived) command
must use `semantic_generation: 0u32` too, or a real hit is refused with
`UI_SCENE_ROUTE_REFUSE_STALE_GENERATION`. If your lane MINTS its own
content and controls both the command and the owner at the same write
site (like L8's menubar items), you may choose any constant — as long as
the command's `component_generation` and the owner's `semantic_generation`
use the exact same value. This was never exercised by any single-producer
spec (each used self-consistent literal fixture values, not real oracle
output) until a cross-producer integration test composed real output.

## Reverse event routing

Once your producer's owners are wired (real hit_shapes + a real
cross-referencing command + correct `host_owner_id`),
`ui_scene_event_route.spl`'s `ui_scene_route_event(scene, resolved, owners,
px, py)` handles the rest unchanged: hit query (reusing
`draw_ir_v3_group_resolve_hit_test`'s reverse/top-most-first,
hidden-group-excluding walk — this returns `cmd.component_id` on a hit,
never `hit_shape.component_id`, so BOTH your hit_shape's own
`component_id` and your owner's `semantic_id` must equal the cross-referenced
command's `component_id` for the lookup to work), owner lookup, the
generation check above, then bubbles the owner chain to the nearest
ancestor carrying a live `action_binding_id`. A producer that never sets
its own `action_binding_id` on a given owner (e.g. a GUI window-chrome
close button) is transparently skipped in favor of whichever ancestor
actually owns that action — no special-cased adapter needed.
