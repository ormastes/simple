# ui_scene_route_event resolves owners by a producer-PRIVATE id with no producer scope

- **Status:** OPEN (filed, not fixed — see "Why not fixed here")
- **Severity:** P2 (latent today; becomes P1 the moment the scene assembler
  wires a real multi-producer scene)
- **Area:** UI / unified packed UI scene, lane L9 reverse event routing
- **Found:** 2026-08-08, UI/render/WM bug-hunt lane

## Symptom

In an assembled scene containing owner records from more than one packed
producer, a pointer event can be routed to the WRONG producer's owner record,
or silently refused with `UI_SCENE_ROUTE_REFUSE_STALE_GENERATION`, even though
the hit itself was correct and the target is live.

## Root cause

`src/lib/common/ui/ui_scene_event_route.spl:60-66`

```
fn _ui_scene_find_owner_by_semantic_id(owners: [UiOwnerRecord], semantic_id: u32) -> i64:
    var i = 0
    while i < owners.len():
        if owners[i].semantic_id == semantic_id:
            return i.to_i64()
        i = i + 1
    -1
```

It returns the FIRST row whose `semantic_id` matches, scanning the whole
shared OWNER_RECORDS table. But `semantic_id` is declared, in
`src/lib/common/ui/ui_scene_owner_table.spl:35`, as a **producer-private node
id** — and `UiOwnerRecord` already carries the disambiguator
(`producer_kind`, field at line 33) that this lookup ignores.

Every producer mints those ids out of its own independent, small-integer id
space, so collisions across producers are not exotic, they are the default:

- `src/lib/common/ui/wm_packed_producer.spl:396,405` — WM copies its oracle's
  hit shapes and writes `semantic_id: comp_id` where `comp_id` comes from the
  WM sub-scene's own `draw_ir_v2_to_v3` id allocator (0-based, sequential).
- `src/lib/common/ui/ui_gui_packed_producer.spl:349,392` — GUI does exactly the
  same thing over ITS sub-scene's allocator, also 0-based.
- `src/lib/common/ui/ui_web_packed_producer.spl:262,271` — likewise for Web.

So WM `semantic_id == 3` and GUI `semantic_id == 3` are different logical
nodes that the lookup cannot tell apart.

Two observable outcomes, both wrong:

1. The colliding rows carry different generations
   (`wm_packed_producer.spl:405` writes `semantic_generation: 0u32` for copied
   hit shapes; `ui_gui_packed_producer.spl:392` writes
   `GUI_INTERACTIVE_GENERATION`). The generation check at
   `ui_scene_event_route.spl:117` then compares the WRONG row's generation
   against the hit command's and refuses with
   `UI_SCENE_ROUTE_REFUSE_STALE_GENERATION` — a live, correctly-hit widget
   stops responding, and the receipt blames staleness rather than the
   ambiguity that actually occurred.
2. The generations happen to agree, the check passes, and the event bubbles up
   the wrong owner chain — reaching a different producer's
   `action_binding_id` (`_ui_scene_chain_action`, line 77).

Note this is genuinely a lookup-scope bug, not an id-allocation bug: WM's own
internal ids are collision-free by construction, and
`_wm_window_owner_base` (`wm_packed_producer.spl:191-192`) is careful to place
window owners past the menubar's range. The defect is only that the resolver
throws that per-producer structure away.

## Why not fixed here

The correct fix scopes the lookup to the producer that owns the winning
command — but `ui_scene_route_event` structurally cannot know that today:
`DrawIrV3GroupResolveResult` carries `component_index`/`component_id`, not a
producer identity, and nothing on the command row records which producer
emitted it. Fixing it means either threading a producer id onto the command or
range rows, or changing the routing signature and every call site. That is a
design decision for the scene ASSEMBLER owner, not a local repair.

It is also not reproducible against real data yet, which is why it is filed
rather than fixed: the module header of `ui_scene_event_route.spl` (lines
31-38) records that L6/L7/L8 all write every `parent_owner_id` as `NO_ID` and
that no producer cross-links a nested producer's root owner to its host — so
no assembled multi-producer scene exists to hit it. Any RED today would be a
synthetic fixture written specifically to fail.

## Unblock condition / definition of done

Fix at the same time as the assembler change that first places two producers'
owner records in one table:

1. Give the resolver a way to learn the producer of the winning command (a
   producer id on the command/range row is the smaller change).
2. Match on `(producer, semantic_id)`, not `semantic_id` alone.
3. Add a distinct refusal reason for "ambiguous owner" so a collision can never
   again be reported as `REFUSE_STALE_GENERATION`.
4. Regression spec: two producers' owner records in one table sharing a
   `semantic_id`, asserting the event reaches the right one and that the other
   producer's action binding is never invoked.

## References

- `src/lib/common/ui/ui_scene_event_route.spl:60-66,104-121`
- `src/lib/common/ui/ui_scene_owner_table.spl:32-38`
- `src/lib/common/ui/wm_packed_producer.spl:394-408`
- `src/lib/common/ui/ui_gui_packed_producer.spl:345-393`
- `src/lib/common/ui/ui_web_packed_producer.spl:260-272`
- Design authority: `doc/05_design/ui/unified_packed_ui_scene.md` sections 2.4, 4.1
- Feature wiki: `doc/00_llm_process/feature_expert/unified_packed_ui_scene/skill.md`
