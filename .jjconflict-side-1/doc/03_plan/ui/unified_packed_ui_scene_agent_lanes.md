# Unified Packed UI Scene — Parallel-Agent Execution Lanes

Status: plan (dispatch document). Design authority:
`doc/05_design/ui/unified_packed_ui_scene.md` (read it before starting any lane).
Research: `doc/01_research/local/unified_packed_ui_scene.md`.

**Status update (2026-08-06): lanes L0-L9 below are all landed** (L6
`1e0a4c18b0b`, L7 `721bc3f579b`, L8 `ed086bb06d4`, L9 `dcd08e77f22`, plus a
cross-producer `host_owner_id`/generation-consistency follow-on). Current
handoff notes and known gotchas:
`doc/00_llm_process/feature_expert/unified_packed_ui_scene/skill.md`.

## Ground rules for every lane (non-negotiable)

1. **File ownership is exclusive.** A lane writes ONLY the paths in its "Owns"
   list. Two lanes have already had edits silently reverted this session by
   concurrent writes — do not touch another lane's files, not even "trivially".
   If a lane discovers it needs a change in a file it does not own, it files a
   note in its report and the owning lane makes the change.
2. **Read-only for ALL lanes** (frozen or owned elsewhere — design §7):
   `src/lib/common/ui/draw_ir_v3.spl`, `draw_ir_v3_ports.spl`,
   `draw_ir_v3_emit.spl`, `draw_ir_v3_oracle.spl`,
   `gpu_web_capacity_manifest.spl`, `gpu_web_capacity_strides.spl`,
   `src/lib/nogc_async_mut/wm/host.spl`.
3. **Commit + push per lane immediately on green** (plumbing CAS per repo VCS
   rules); verify file content by grep before committing — a parallel process
   can revert files mid-session.
4. **Gate discipline** (applies to every gate below): capture the full run to a
   file; the authoritative receipt is the stderr/stdout line
   `SPEC FILE VERDICT: <path> declared>=N executed=N passed=N failed=N dropped=N`.
   Match it with `/usr/bin/grep -a "SPEC FILE VERDICT"` (lines are ANSI-wrapped;
   never `tail -1`; never anchor a numeric regex at line start). A gate passes
   only when **executed equals the lane's declared floor AND failed=0 AND
   dropped=0** — compare COUNTS, not just failures; a module-load failure drops
   whole describes at exit 0. Run with `--no-cache --no-cover-check` (shared
   manifest races between concurrent lanes otherwise produce "0 total" at exit
   0). Exit 255/143 with no output = timeout/kill, not a verdict. Exit status is
   fail-open (unresolved `use` is a WARN); the verdict line is the only oracle.
   No bare `assert` (inert); no `check(true)` vacuity; `pending()` never counts
   as failure — a pending example does not satisfy an executed-count floor.
5. **Sabotage check is mandatory before declaring a lane done.** Apply the
   listed sabotage, re-run the gate, confirm the verdict goes to `failed>=1` (or
   the executed-count floor breaks), then revert the sabotage and re-confirm
   green. A gate that stays green under sabotage has proved nothing — report
   that as a lane FAILURE, not a pass.
6. **WML001/WML002 lint ratchet**: any lane creating WM-adjacent modules runs
   `bin/simple lint <its new files>` and must add **zero** entries beyond the
   219-entry baseline.

## Lane graph

```
Wave 0 (immediate):      L0 docs   L1 vocabulary   L2 group-resolver   V validation(sibling, running)
Wave 1 (after L1):       L4 emit-full     L5 arena+writers     L3 v2→v3 adapter (gate also needs L2)
Wave 2 (after L1+L4+L5): L6 GUI producer      L7 Web producer
Wave 3 (after L6, +L1):  L8 WM background + menubar     L9 reverse event routing (after L4+L5+L6)
Not yet:                 retained/dirty (Ph7), Vulkan (Ph8), cutover (Ph9) — see §Not-worth-yet
```

Dependency edges (blocked-by): L3←{L1,L2}; L4←L1; L5←L1; L6←{L1,L4,L5};
L7←{L1,L4,L5}; L8←{L1,L6}; L9←{L4,L5,L6}. L0, L1, L2 have no dependencies and
are **dispatchable now**. L6 and L7 are mutually independent (disjoint files) —
run concurrently. If the sibling validation lane (V) falsifies an assumption
A1–A5, only the containment listed in design §0.1 changes — no lane is blocked
on V.

---

## L0 — Doc reconciliation (Phase 0)

**Value/risk:** low effort, prevents four planning docs from diverging from the
frozen decision. Do first because it is pure-doc and conflict-free.

**Owns:** `doc/03_plan/ui/webir_drawir_optimization.md`,
`doc/03_plan/ui/draw_ir/**` reconciliation/native-refactor plan docs,
`doc/05_design/ui/rendering/rendering_inside_rendering*.md` (whichever of these
exist — locate exact paths first; touch nothing outside `doc/`).

**Task:** append a short "Superseded-by/decided" note to each affected plan doc
pointing at the design doc's 7 decisions. No runtime changes.

**Gate:** `sh scripts/check-workspace-root-guard.shs` exits 0, and
`/usr/bin/grep -l "unified_packed_ui_scene" <each edited doc>` lists every
edited file. **Sabotage:** point one note at a nonexistent path; the grep-based
link check (`test -f` on each referenced path in the note) must go RED.
**Size (estimate):** 1 agent-session, ~5 doc edits.

## L1 — Scene vocabulary (foundation; Phase 2/3 types)

**Value/risk:** highest — every other code lane imports these types. Pure value
code, zero runtime coupling, so risk is minimal. Dispatch first.

**Owns (new files only):**
`src/lib/common/ui/ui_scene_counts.spl`,
`src/lib/common/ui/ui_scene_slice.spl`,
`src/lib/common/ui/ui_scene_owner_table.spl`,
`src/lib/common/ui/ui_scene_prepared2d.spl`,
`src/lib/common/ui/draw_ir_v3_ports_v2.spl`,
`test/01_unit/lib/common/ui/ui_scene_types_spec.spl`,
`test/01_unit/lib/common/ui/ui_scene_ports_v2_spec.spl`.

**Task:** implement design §2 exactly: counts/ranges/table-ids, exclusive
prefix-scan + verify functions, overflow receipt, slice, producer + writer
traits, owner/action records with generation-validated dispatch check (pure),
Prepared2D types, `PackedSceneRef` + `PackedDrawPortV2` trait +
`DrawIrV3SubmitReceipt`. NO arena, NO backend impls.

**Gate:**
```
bin/simple test test/01_unit/lib/common/ui/ui_scene_types_spec.spl \
  test/01_unit/lib/common/ui/ui_scene_ports_v2_spec.spl \
  --no-cache --no-cover-check > /tmp/l1.log 2>&1; /usr/bin/grep -a "SPEC FILE VERDICT" /tmp/l1.log
```
Receipt: two verdict lines, each `failed=0 dropped=0`, combined `executed>=20`.
Required assertions (not "add tests" — these specific ones): (a) scan of counts
{3,0,5} for one table yields disjoint, gapless ranges {0..3},{3..3},{3..8};
(b) verify with required>capacity returns a receipt with the correct
`table_id/required/capacity` and emits nothing; (c) a stale
`app_generation` in `MenuActionBinding` validation returns refusal, fresh one
passes; (d) `UiSceneTableId` numbering matches design §2.1 literally (pin all
16 values — this is a cross-module ABI).

**Sabotage:** (1) make the scan inclusive instead of exclusive → assertion (a)
RED; (2) make verify clamp `required` to `capacity` instead of refusing →
assertion (b) RED. Both must go RED individually.
**Size (estimate):** 1–2 agent-sessions, ~700–1,100 lines incl. specs.

## L2 — GROUP/PORT resolver + conformance (Phase 1 core)

**Value/risk:** high value (windows/scrolling/menus all hang off GROUP), medium
risk (assumption A3). Dispatchable now — depends only on the frozen v3 schema.

**Owns:** `src/lib/common/ui/draw_ir_v3_group_resolve.spl`,
`test/01_unit/lib/common/ui/draw_ir_v3_group_resolve_spec.spl`.

**Task:** first a capability-probe spec recording what the existing CPU
executor already does with GROUP/PORT (A3 containment — if semantics exist,
this lane becomes conformance + gap-fix against design §4, not a rewrite).
Then implement design §4 exactly: parent∘local transform order, AABB clip
intersection, u16 multiplicative opacity, AND-visibility excluding hit testing,
contiguous-descendant structural check (receipt on violation),
`NEEDS_OFFSCREEN` marking with refuse-don't-degrade, PORT as leaf with
surface_id+generation and loud-marker on unavailable.

**Gate:**
```
bin/simple test test/01_unit/lib/common/ui/draw_ir_v3_group_resolve_spec.spl \
  --no-cache --no-cover-check > /tmp/l2.log 2>&1; /usr/bin/grep -a "SPEC FILE VERDICT" /tmp/l2.log
```
Receipt: `failed=0 dropped=0 executed>=18`. Required assertions: (a) a point in
a child of a translated group hits at translated world coords and misses at
local coords; (b) nested groups compose in parent∘local order — a specific
asymmetric pair where the wrong order yields a DIFFERENT numeric position,
asserted to the correct one; (c) invisible group: descendant neither batched
nor hit; (d) rotated group with clip → `NEEDS_OFFSCREEN` set, and a
non-supporting executor path returns refusal, not a dropped clip; (e)
non-contiguous child range → STRUCTURE receipt; (f) stale PORT surface
generation → loud marker command present in output + receipt.

**Sabotage:** (1) swap composition to local∘parent → (b) RED; (2) make
invisible groups still hit-testable → (c) RED; (3) drop the clip instead of
marking NEEDS_OFFSCREEN → (d) RED.
**Size (estimate):** 2 agent-sessions, ~800–1,400 lines incl. specs.

## L3 — v2→v3 typed adapter + pixel parity (Phase 1 bridge)

**Blocked by:** L1 (receipt types), L2 (executor must resolve GROUP for the
parity corpus). RECT/TEXT-only adapter work may start once L1 lands; the gate
requires L2.

**Owns:** `src/lib/common/ui/draw_ir_v2_to_v3.spl`,
`test/01_unit/lib/common/ui/draw_ir_v2_to_v3_spec.spl`,
`test/02_integration/ui/draw_ir_v2_v3_pixel_parity_spec.spl`.

**Task:** typed (no cast) adapter `DrawIrComposition(v2) → DrawIrV3Scene`
covering RECT, TEXT, IMAGE/resources, PATH, GROUP, PORT, clips, transforms, hit
shapes. Parity corpus: at least one WM scene, one GUI widget scene, one Web
scene rendered through the existing v2 CPU path and through adapter+v3 CPU
executor.

**Gate:**
```
bin/simple test test/02_integration/ui/draw_ir_v2_v3_pixel_parity_spec.spl \
  --no-cache --no-cover-check > /tmp/l3.log 2>&1; /usr/bin/grep -a "SPEC FILE VERDICT" /tmp/l3.log
```
Receipt: `failed=0 dropped=0 executed>=6`, where each corpus example asserts
`v2_pixels == v3_pixels` as a full-buffer byte comparison AND asserts the
buffer is non-trivial (`nonzero_pixel_count > 0` — an all-zero==all-zero pass
is vacuous and forbidden).

**Sabotage:** make the adapter drop GROUP transforms (emit identity) → parity
RED on the WM corpus example. If it stays green, the corpus does not exercise
GROUP — fix the corpus, not the assertion.
**Size (estimate):** 2 agent-sessions, ~900–1,500 lines.

## L4 — Full-schema exact-size emitter (Phase 2)

**Blocked by:** L1. Concurrent with L5, L3.

**Owns:** `src/lib/common/ui/draw_ir_v3_emit_full.spl`,
`test/01_unit/lib/common/ui/draw_ir_v3_emit_full_spec.spl`.

**Task:** a NEW emitter (A–E `draw_ir_v3_emit.spl` stays untouched as oracle)
that counts and writes ALL 16 tables via the L1 scan/verify path, enforces
emitted==counted per table (Deficit/Surplus verdicts), produces overflow
receipts, allocates stable component IDs. Uses `UiSceneCapacityExtensionV1`
sidecar; never touches the frozen manifest.

**Gate:**
```
bin/simple test test/01_unit/lib/common/ui/draw_ir_v3_emit_full_spec.spl \
  --no-cache --no-cover-check > /tmp/l4.log 2>&1; /usr/bin/grep -a "SPEC FILE VERDICT" /tmp/l4.log
```
Receipt: `failed=0 dropped=0 executed>=16`. Required assertions: (a) for a
fixture scene, EVERY table the fixture logically needs is non-empty (pin exact
row counts per table — this is the anti-regression against the current
empty-side-tables emitter); (b) same input twice → byte-identical output
(determinism); (c) capacity one row short on HIT_SHAPES → CAPACITY receipt
naming HIT_SHAPES, zero rows written anywhere; (d) a producer stub that writes
counted-1 rows → DEFICIT verdict, generation invalid; counted+1 → SURPLUS.

**Sabotage:** (1) skip the hit-shape table write → (a) RED; (2) on overflow,
truncate instead of refuse → (c) RED; (3) accept a deficit as success → (d)
RED.
**Size (estimate):** 2–3 agent-sessions, ~1,200–2,000 lines.

## L5 — Session arena + native writers + port-v2 impl (Phase 3)

**Blocked by:** L1. Concurrent with L4.

**Owns:** `src/lib/nogc_sync_mut/ui/ui_scene_arena.spl`,
`src/lib/nogc_sync_mut/ui/draw_ir_v3_native_writer.spl`,
`test/01_unit/lib/nogc_sync_mut/ui/ui_scene_arena_spec.spl`.

**Task:** design §3: allocate-once arena from `UiSceneCapacityExtensionV1`,
front/back generations with completion-gated swap, `UiSceneLease` views,
bounds-checked cursor writers, a `PackedDrawPortV2` implementation submitting
`PackedSceneRef` (slot+generation), v1 compatibility adapter for tests.

**Gate:**
```
bin/simple test test/01_unit/lib/nogc_sync_mut/ui/ui_scene_arena_spec.spl \
  --no-cache --no-cover-check > /tmp/l5.log 2>&1; /usr/bin/grep -a "SPEC FILE VERDICT" /tmp/l5.log
```
Receipt: `failed=0 dropped=0 executed>=14`. Required assertions: (a) two
generations written back-to-back reuse the same buffers — assert the arena's
allocation counter is unchanged after warm-up (counter exposed by the arena for
exactly this gate; allocation claims are counted in-band, never inferred from
timing); (b) write past a reserved range returns false and invalidates the
generation; (c) swap before completion-signal is refused; after signal it
succeeds; (d) a `PackedSceneRef` with stale `object_generation` is refused by
submit with a receipt, fresh one accepted; (e) v1 adapter round-trip matches
direct v1 submission.

**Sabotage:** (1) make the arena reallocate per generation → (a) RED; (2) allow
swap without completion → (c) RED; (3) accept stale generation refs → (d) RED.
**Size (estimate):** 2–3 agent-sessions, ~1,000–1,800 lines.

## L6 — GUI producer adoption (Phase 4, GUI half)

**Blocked by:** L1, L4, L5.

**Owns:** `src/lib/common/ui/ui_gui_packed_producer.spl` (new; adapters call
INTO existing widget code — this lane does not edit the widget tree files),
`test/01_unit/lib/common/ui/ui_gui_packed_producer_spec.spl`.

**Task:** `UiPackedProducer` for the widget tree/Panel2D path; existing public
functions (`widget_tree_to_draw_ir`) remain as compatibility adapters and the
v2 oracle. Every emitted interactive command gets an owner record; nested-child
producer invocation (count-in-count, emit-in-ranges) proven with a stub child.

**Gate:** same command shape on its spec; receipt `failed=0 dropped=0
executed>=12`. Required assertions: (a) count is repeatable and emit fills
exactly counted rows (finish()==Exact); (b) every hit-shape row emitted has an
owner record with `producer_kind==GUI` and a live `semantic_generation`; (c) a
stub child producer's rows land inside the parent-assigned sub-ranges and
nowhere else; (d) pixel parity of producer output vs
`widget_tree_to_draw_ir`+v2→v3 adapter on one widget corpus (non-trivial
buffer, as L3).

**Sabotage:** (1) emit a button with no owner record → (b) RED; (2) let the
child write one row past its sub-range → (c) RED.
**Size (estimate):** 2–3 agent-sessions, ~1,000–1,600 lines.

## L7 — Web producer adoption (Phase 4, Web half)

**Blocked by:** L1, L4, L5. Fully concurrent with L6 (disjoint files).

**Owns:** `src/lib/common/ui/ui_web_packed_producer.spl` (adapter over the
existing final-paint lowering; does NOT edit Web parser/CSS/layout files),
`test/01_unit/lib/common/ui/ui_web_packed_producer_spec.spl`.

**Task/gate/sabotage:** mirror of L6 with `producer_kind==WEB`, plus one
WebView-nesting example: GUI stub host + Web producer child in ONE arena,
asserting the Web root's `parent_id` is the host WebView component and that no
intermediate command array was allocated (arena allocation counter unchanged
during the nested emit). Receipt `failed=0 dropped=0 executed>=12`.
**Sabotage:** make the Web producer allocate its own command buffer and copy →
allocation-counter assertion RED.
**Size (estimate):** 2–3 agent-sessions, ~1,000–1,600 lines.

## L8 — WM background + global menubar (Phase 5)

**Blocked by:** L1, L6 (menubar is a GUI shell producer).

**Owns:** `src/lib/common/ui/app_menu_snapshot.spl`,
`src/lib/nogc_sync_mut/ui/app_menu_registry.spl`,
`src/lib/nogc_async_mut/wm/wm_packed_producer.spl` (new; reads existing WM
state, edits no existing WM file),
`test/01_unit/lib/common/ui/app_menu_snapshot_spec.spl`,
`test/02_integration/ui/global_menubar_spec.spl`.

**Task:** WM direct background emit (1 retained RECT or IMAGE+resource; failed
provider keeps the loud marker); flat `AppMenuSnapshot`/registry;
global-menubar producer bound to `active_app_id`; `command_lane` kept as
untouched legacy geometry alias (assumption A4). `bin/simple lint` on all new
files: zero WML001/WML002 entries beyond the 219 baseline.

**Gate:** receipt `failed=0 dropped=0 executed>=14` on the two specs combined.
Required assertions: (a) exactly one menubar surface exists after composing two
windows + taskbar (count menubar-segment groups == 1); (b) switching
`active_app_id` changes left-menu item rows and does NOT change background,
taskbar, or window-content ranges (assert those ranges byte-identical across
the switch); (c) menu action dispatch with matching generations reaches the
active app's binding; stale `menu_revision` is refused; (d) failed background
provider → loud marker command present, no substitute background.

**Sabotage:** (1) emit the menubar per-window → (a) RED; (2) on app switch,
also rewrite the taskbar range → (b) RED; (3) substitute a default wallpaper on
provider failure → (d) RED.
**Size (estimate):** 3 agent-sessions, ~1,500–2,500 lines.

## L9 — Reverse event routing (Phase 6)

**Blocked by:** L4 (hit shapes populated), L5 (arena), L6 (owner records).
Ideally after L7/L8 land for corpus breadth, but dispatchable on L6 alone.

**Owns:** `src/lib/common/ui/ui_scene_event_route.spl`,
`test/01_unit/lib/common/ui/ui_scene_event_route_spec.spl`.

**Task:** hit query → `component_id`+generation → owner-chain walk →
producer-local dispatch, per design §2.4/§4.1 hit rules. Window-chrome close
routes GUI button → chrome adapter → WM action (GUI never mutates
WindowManager directly).

**Gate:** receipt `failed=0 dropped=0 executed>=12`. Required assertions: (a)
same component identity across paint row, hit shape and routed event for a
fixture button; (b) stale `component_generation` on a hit → event dropped with
routed-refusal, never delivered to the recycled slot; (c) WebView chain walks
Web→GUI host→WM in that order (assert the visited owner-id sequence); (d) a
click on a hidden group's former area routes to what is beneath, not the hidden
owner.

**Sabotage:** (1) skip generation validation → (b) RED; (2) walk composition
order instead of reverse → (c) RED.
**Size (estimate):** 2 agent-sessions, ~800–1,400 lines.

---

## Not worth doing yet (deliberate, revisit after Wave 2 lands)

- **Phase 7 retained segments / dirty-byte patches / occlusion culling** — the
  patch vocabulary exists (L1 DIRTY_RANGES), but building revision plumbing
  before L6/L7 producers exist is infrastructure without a consumer. Lane it
  only after both producers are green.
- **Phase 8 Vulkan S3/S4 native execution** (SFFI, persistent descriptors,
  SSBO batching, dirty upload) — blocked on everything above and on hardware
  evidence discipline; premature laning invites QEMU-only/board-gap debt
  (`.claude/rules/board-runnable.md`).
- **Phase 9 production cutover / legacy painter removal** — not plannable until
  parity evidence exists.
- **Vulkan Tier 1/2, cross-process PORT, SimpleOS IPC menus, motion wallpaper,
  menu DSL** — speculative per design §8; no consumer.

## Dispatch summary

| Now | After L1 | After L1+L4+L5 | After L6 |
|---|---|---|---|
| L0, L1, L2 | L4, L5, L3(gate also needs L2) | L6 ∥ L7 | L8, L9 |

Total: 10 lanes (L0–L9), ~19–27 estimated agent-sessions, all sizes estimates.
Highest value-per-risk first: L1 (everything depends on it, pure code), L2
(unlocks the parity gate and all GROUP-based wins), L0 (cheap divergence
insurance). L8 carries the most integration risk (WM lint ratchet + A4) — do
not start it before L6's owner-record contract is proven.
