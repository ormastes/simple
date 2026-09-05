# Unified Packed UI Scene Feature Expert

## Role

Own feature-specific process knowledge for the unified packed UI scene
campaign: one physical DrawIR-v3 arena per session, written by disjoint
pre-reserved ranges from WM, GUI, Web and future producers via the
`UiPackedProducer` trait (`count()`/`emit()`), instead of each front end
owning a separate scene.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)
- [pipeline next step plan](../../pipeline_next_step_plan.md)

## Feature Links

- Design authority: [doc/05_design/ui/unified_packed_ui_scene.md](../../../05_design/ui/unified_packed_ui_scene.md)
- Agent lane plan: [doc/03_plan/ui/unified_packed_ui_scene_agent_lanes.md](../../../03_plan/ui/unified_packed_ui_scene_agent_lanes.md)
- Practical producer-writing guide: [doc/07_guide/ui/rendering/unified_packed_ui_scene_producers.md](../../../07_guide/ui/rendering/unified_packed_ui_scene_producers.md)
- Layer expert: [layer_expert/ui_render](../../layer_expert/ui_render/skill.md)
- Source: `src/lib/common/ui/ui_scene_slice.spl` (trait), `ui_gui_packed_producer.spl` (L6),
  `ui_web_packed_producer.spl` (L7), `wm_packed_producer.spl` (L8),
  `ui_scene_event_route.spl` (L9), `app_menu_registry.spl` / `app_menu_snapshot.spl` (L8).

## Status (2026-08-06)

Lanes L0-L9 all landed:
- L6 GUI producer: `1e0a4c18b0b`
- L7 Web producer: `721bc3f579b`
- L8 WM/menubar producer: `ed086bb06d4`
- L9 reverse event routing (`ui_scene_event_route.spl`): `dcd08e77f22`
- Cross-producer `host_owner_id` wiring + `component_id`/generation
  consistency follow-on (this entry's Gotchas below): landed `dfd465a7125`
  — closes the gap L9's own landing commit documented (every
  producer wrote `parent_owner_id: DRAW_IR_V3_NO_ID`, so L9's WebView-chain
  gate was only proven against a hand-built fixture, not real nested
  producer output). See `test/02_integration/ui/unified_packed_scene_nesting_spec.spl`.

- L6 interactive-widget hit-shape reachability fix (Gotcha 6 below): landed
  `b11002b7eeb`.

Not started: a real multi-producer *assembler* module (today, composing
real producer output is only proven inline in the integration spec above).

## Gotchas

1. **Minted/copied ids must be arena-absolute.** Every table-row-index
   field must be rebased by `ranges.<table>.start` before writing;
   `component_id`/`parent_id`/`semantic_id` are identities, never rebased
   at the single-producer-write level. Single-producer tests can't catch a
   missing rebase (`ranges.<table>.start == 0` when there's only one
   producer). Full pattern: the producer guide's "Mistake 1".

2. **`commands[0]` of a composed v2 batch is a GROUP wrapper**, not
   paintable content — `draw_ir_v2_to_v3` wraps every v2 batch in one v3
   GROUP. Walk to `commands[i].parent_id == commands[0].component_id` to
   find the batch's real content. Guide's "Mistake 2".

3. **GUI/Web hit-testability is asymmetric.** Web's v2 oracle already
   marks ordinary boxes hit-testable; GUI's oracle never sets `hit_rect` —
   GUI locates interactive widgets itself via `kind_name()`. Guide's
   "Mistake 3".

4. **Cross-producer `component_id` collision (found composing real WM+GUI+Web
   output, not caught by any single-producer spec).** Each producer's own
   oracle independently starts its own `component_id` counter at 0, so
   naive concatenation of multiple producers' commands collides ids across
   producers, and `draw_ir_v3_group_resolve` returns `ok=false, states=[]`
   (breaks structural parent-child matching) — which then crashes
   `ui_scene_route_event` indexing into the empty `states` array. Fix: each
   producer's command/hit_shape `component_id`/`parent_id`, AND the
   matching owner `semantic_id`, need a per-producer offset before
   combining (offset = running total of commands already appended — not a
   magic constant, collision-free by construction). No assembler module
   exists yet to hold this; `unified_packed_scene_nesting_spec.spl` does it
   inline and says so in its own comment. **Whoever builds a real
   multi-producer assembler must do this same offsetting.**

5. **Owner `semantic_generation` must EQUAL the hit command's
   `component_generation`, not just be non-zero.** L9's "recycled slot"
   check in `ui_scene_event_route.spl` does an equality comparison. Every
   command `draw_ir_v2_to_v3` emits carries `component_generation: 0u32`
   unconditionally (both of its command-construction sites) — so any owner
   record backed by an oracle-copied command must use `semantic_generation:
   0u32`, not a nonzero "live" constant, or every real hit is refused with
   `UI_SCENE_ROUTE_REFUSE_STALE_GENERATION`. This was never exercised until
   the cross-producer integration spec (every landed single-producer spec
   used self-consistent literal fixture values, not real oracle output).
   Two values legitimately coexist in `wm_packed_producer.spl`: minted
   content (menubar items — this lane controls both the command and the
   owner at the same write site, so both use `WM_OWNER_GENERATION`) vs.
   copied content (existing hit-shapes from the oracle — command generation
   is 0u32 from the oracle, so the owner must also be 0u32). Web's single
   generation constant (`WEB_HIT_OWNER_GENERATION`) was simply wrong (1u32)
   and is now 0u32 to match.

6. **Closed: GUI's interactive-widget hit shapes were unreachable by the
   L9 router** (`draw_ir_v3_group_resolve_hit_test` only considers
   commands whose own `hit_shape_id` is set; GUI's synthetic
   interactive-widget hit_shapes had no backing command cross-referencing
   them, since the widget-tree oracle never emits `hit_rect`). Fixed by a
   real cross-reference instead of a generation tweak:
   `draw_ir_v2_to_v3.spl` gained ONE small additive export,
   `draw_ir_v2_to_v3_command_ids_for(composition, component_ids: [text]) ->
   [u32]` (no existing signature changed) — it re-runs the SAME
   deterministic id-assignment pass `draw_ir_v2_to_v3` uses internally and
   looks up each requested v2 text `component_id` (e.g. a widget's own
   `rect.id`; the FIRST command `_emit_widget` pushes per kind is
   button/input/textfield: `rect.id` itself, checkbox: `"{rect.id}-box"`)
   in the resulting map. `ui_gui_packed_producer.spl` uses this to find
   the real command that draws each interactive widget and patches THAT
   command's `hit_shape_id` to point at the widget's synthetic hit_shape
   row (`_gui_find_command_index` + a per-command-index override array,
   computed before the main command-writing loop since existing hit_shapes
   are written first at a statically-known offset — no writer cursor
   needed). Also aligned `GUI_INTERACTIVE_GENERATION` to `0u32` (same
   reasoning as Gotcha 5's Web/WM fix, since these commands now really are
   cross-referenced and come from the same oracle). New regression test:
   `ui_gui_packed_producer_spec.spl`'s "interactive-widget hit shapes are
   reachable via L9 routing" — builds a real scene, runs
   `draw_ir_v3_group_resolve` + `ui_scene_route_event` against a click on
   the button's own hit_shape rect, asserts `accepted: true`.

## Update Rule

When research, requirements, architecture, design, tests, implementation,
verification, or release artifacts for this feature change, update this
skill with the new links and current handoff notes — especially the
Gotchas above, since each cost a real debugging cycle to find.
