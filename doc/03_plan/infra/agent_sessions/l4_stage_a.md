# Lane: L4 Stage A — Simple 2D event hardening / DrawIR (ex-claude 243d611f)

Goal (session `/goal`, verbatim): "1. simple event handling harden through
simple 2d. 2. simple 2d planel which used internal window, task bar, in game
object. layer, scollable pabel. transparent panel. 3. event forward through
object(drawir composed, group), collitiin detect. 4. simple 2d highly
offloadable. 5. all game and gui(thorugh web) renderer needed feature exidts.
drawir full supported. 6. with vulkan/cuda fully offload 2d processing and event
forward to gpu. check exist plan and arch. first research and improve
arch/design. and bit/vector font to use. do with pherallel agents"

Governing plan doc: `doc/03_plan/ui/webir_drawir_optimization.md` (Phase 0..5).
Session self-audit: scratchpad `PHASE2_STATUS.md` (Phase 2 refresh vs origin).

## Plan audit 2026-08-01

### Registry correction (do this first)
`groups.md` said "DONE but NOT PUSHED — local commit `926515796c6` absent from
origin/main; must land". **That is wrong and landing it would be destructive.**
`926515796c6` has an EMPTY subject line and is a 504-file whole-working-copy
snapshot with **34,700 deletions** — the exact stale-WC clobber pattern
`.claude/rules/vcs.md` § "Sync must never clobber" forbids. Do not land it.

The session's real work IS on `origin/main`:
- `44b41ef9f56c` feat(2d): CSS-reachable gradients, tilemap texel sampling,
  DrawIR affine stage 1 (game2d extern fix, 14 call sites, 6 dead `@extern`
  removed, `batch_flush_position_spec`, five bug reports)
- `bd1a953e6952` feat(ui/draw-ir): thread `parent_id` through the leaf DrawIR
  command builders (13 examples / 0 failures)

### Verified closed
- Phase 2 `<img>` → `DRAW_IR_COMMAND_IMAGE`: DONE.
- Phase 2 `parent_id` from parent node: DONE on main — producer wires it at
  `simple_web_html_layout_renderer_paint_layout.spl:2380-2387`, and the 7 leaf
  builders in `src/lib/common/ui/draw_ir.spl` take a defaulted parameter.
- Phase 2 iframe-as-embedded-batch: DONE, but not the way `PHASE2_STATUS.md`
  predicted — closed by flattening in `_simple_web_layout_compose_document` →
  `draw_ir_embed_composition` (present on main in `src/lib/common/ui/draw_ir.spl`
  and `simple_web_html_layout_renderer.spl`). The status doc's claim that
  `_engine2d_draw_ir_render_batch_embedded` was "exactly the mechanism" was
  wrong; the schema has no nested-batch reference.

### MISSING — the session was killed mid-flight with 4 lanes running
1. **`texture_registry` spec fails 6 of 10.** The session pulled it from its
   landing set but `src/lib/gc_async_mut/game2d/texture_registry.spl` and
   `test/01_unit/lib/gc_async_mut/game2d/texture_registry_spec.spl` are BOTH
   still on `origin/main`. Next: re-run the spec; fix, or delete both files
   (nothing on main imports the module, so deletion is legitimate under the
   no-unused-code rule).
2. **GAP-2 gradient engine wrapper never landed.** `draw_gradient_rect_stops`
   is defined **nowhere** in `src/` on `origin/main`, yet the reverted graft
   called it. Gradient-stop handling that DID land went a different route
   (`engine2d/engine.spl`, `backend_emu.spl`). Next: confirm the CSS n-stop /
   angled / radial path is genuinely reachable end-to-end, or add the missing
   `Engine2D` wrappers over the existing `emu_*` primitives. The reverted graft
   is preserved in the session scratchpad.
3. **`draw_ir_adv_spec` 3 failures were never baselined.** The haiku
   measurement lane was killed before reporting. Next: run it and record
   whether those 3 are pre-existing.
4. **Phase 2 pixel-parity corpus (images + iframes) does not exist.** It is the
   stated acceptance gate for both closed Phase 2 items — they are currently
   accepted on code inspection only.
5. **Phase 0 determinism still blocks every bit-exact parity gate**
   (`web_render_full_engine_call_order_nondeterminism_2026-07-12.md`). Phases
   3-5 cannot start until it closes.
6. **Phase 3 perf numbers are blocked on tooling** — the plan requires
   self-hosted `bin/simple`, which is bootstrap-only.
7. **Goal items 4/6 (Vulkan/CUDA full 2D + event-forward offload) and item 2
   (internal window / task bar / layer / scrollable / transparent panel) were
   never reached.** The session spent its budget on Phase 2 gaps and on
   recovering from the `origin/main` tree wipe. Not de-scoped — just not done.
8. **Housekeeping flagged for the user, still open:** `.git` is 55 G with
   153,450 loose objects and gc disabled by a stale `gc.log`; the session
   declined to `git prune` on a repo other sessions are writing.

## sspec coverage 2026-08-01

Audit of the session's six goal items against runnable sspec system tests
present on `origin/main` (unit/integration specs under `test/`). "Covered"
means a spec exercises the item's shipped code; it does not claim the item
itself is complete.

1. **Event hardening through simple 2d — covered.**
   `test/01_unit/lib/common/engine/interaction/window_event_adapter_spec.spl`,
   `hit_grid_u32_spec.spl`, `test/01_unit/lib/common/ui/gpu_event_core_spec.spl`,
   `test/01_unit/lib/{gc,nogc}_async_mut/gpu/engine2d/host_gpu_event_queue_spec.spl`.
2. **Panels (internal window, task bar, layer, scrollable, transparent) — partial.**
   Covered: `panel2d_spec.spl`, `panel2d_text_spec.spl`,
   `window_scene_draw_ir_panel2d_migration_spec.spl`,
   `window_scene_draw_ir_layer_order_spec.spl`, `window_scene_close_lifecycle_spec.spl`.
   MISSING scenarios: task-bar panel behavior, scrollable-panel scrolling,
   transparent-panel compositing, internal window driven by an in-game object.
   (Goal item 2 itself was never reached — see MISSING item 7 above.)
3. **Event forward through DrawIR objects/groups + collision — partial.**
   Covered: `draw_ir_hit_bridge_spec.spl`, `host_gpu_hit_query_spec.spl`,
   `host_gpu_hit_query_grid_parity_spec.spl`. MISSING scenarios: event
   forwarding through *grouped/composed* DrawIR nodes, and any
   object-vs-object collision-detection spec (none exists under game2d).
4. **Highly offloadable 2d — partial.** Covered:
   `backend_lane_spec.spl`, `sosix_gpu_lane_route_spec.spl`,
   `font_offload_preference_smoke_spec.spl`, `bitmap_font_offload_spec.spl`,
   `vector_font_offload_spec.spl`,
   `test/02_integration/rendering/engine2d_gpu_offload_evidence.spl`.
5. **Renderer feature completeness / DrawIR full support — partial.**
   Covered: `draw_ir_adv_spec.spl`, `gradient_stops_paint_spec.spl`,
   `simple_web_html_layout_renderer_foundation_gradient_spec.spl`, and (landed
   with this commit) `browser_renderer_gradient_stops_wiring_spec.spl` closing
   the GAP-2 middle (CSS→Style→paint props→draw_ir_adv→Engine2D stops).
   `texture_registry_spec.spl` + `tilemap_spec.spl` cover texel sampling.
   MISSING: the Phase 2 pixel-parity corpus (images + iframes) — still the
   acceptance gate for the two closed Phase 2 items (MISSING item 4 above);
   `draw_ir_transform_spec.spl` exists only in the session scratchpad, not on
   main.
6. **Vulkan/CUDA full 2D offload + GPU event forward — contract-level only.**
   Covered (contracts, not behavior): `test/01_unit/check/vulkan_engine2d_frame_batch_contract_spec.spl`,
   `vulkan_engine2d_readback_mode_contract_spec.spl`,
   `vulkan_2d_benchmark_batch_contract_spec.spl`, `vulkan_renderer_spec.spl`.
   MISSING scenarios: CPU↔Vulkan and CUDA↔Vulkan render-parity specs (the
   killed haiku lane's `l7_*_parity` logs were never landed as specs), and any
   end-to-end "2D pipeline + event forward actually offloaded to GPU" system
   test. Goal items 4/6 were never reached (MISSING item 7 above).

Defect salvage landed with this note:
- `texture_registry` "6/10 failures" reproduce only against a STALE working
  copy whose `tilemap.spl` predates `44b41ef9f56c` (no `TextureRegistry`
  import/field). Module, spec, and textured tilemap on `origin/main` are
  consistent; nothing to fix in the module.
- `draw_gradient_rect_stops` / `draw_radial_gradient_rect_stops` exist on main
  (`engine2d/engine.spl`) but had ZERO callers: the CSS wiring
  (Style stop fields → decl apply parse → paint_layout props → draw_ir_adv
  consumption) was killed with the session. Re-landed minimally from the
  session's proven scratchpad graft, wiring-only (no unrelated reverts), plus
  the wiring spec named above.
