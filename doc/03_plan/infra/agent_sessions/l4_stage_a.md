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
