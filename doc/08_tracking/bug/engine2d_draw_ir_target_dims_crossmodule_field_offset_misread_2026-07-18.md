# BUG: `Engine2D.width()/height()` read garbage cross-module inside `_engine2d_draw_ir_render_batch_embedded` — `fills_target_exactly` always false (currently harmless, masked by `baremetal_direct`)

**Status:** OPEN — low severity (currently harmless; `baremetal_direct` routing masks it)
**Severity:** low today / would become medium if a translucent full-page batch needs the `fills_target_exactly` fast path
**Component:** `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl` — `_engine2d_draw_ir_render_batch_embedded`'s target-dims read, on the SimpleOS x86_64 baremetal/freestanding render path
**Family:** same class as [`simpleos_native_build_framebufferdriver_crossmodule_field_offset_shift_2026-07-14.md`](simpleos_native_build_framebufferdriver_crossmodule_field_offset_shift_2026-07-14.md) — a cross-module struct field read landing on the wrong slot at whole-program scale (the "receiver-blind, most-fields-declaring-this-name-wins" ambiguous field-index scan documented there).
**Found:** 2026-07-18, while verifying the glass-desktop coverage fix (12.64% -> 99.83% non-black), via the gated `[route-dbg]` probe already present in `draw_ir_adv.spl`.

## Symptom

The gated `[route-dbg]` probe (`_engine2d_route_dbg`, `draw_ir_adv.spl:41-44`,
call site `draw_ir_adv.spl:680`) logs every Draw IR batch's embedding vs.
target dims at the `_engine2d_draw_ir_render_batch_embedded` routing decision
point. With `ENGINE2D_DRAW_IR_ROUTE_DBG` flipped to `true`, the desktop batch
logs:

```
[route-dbg] sid= ew=3840 eh=2160 tw=158239601 th=3840 op=1000 clip=false bd=true fte=false ues=false
```

- `ew`/`eh` (`embedding_width`/`embedding_height`, read from
  `batch.embedding.width`/`.height`) are **correct**: `3840`/`2160`.
- `op` (`embedding_opacity`, `batch.embedding.opacity_milli`) is **correct**:
  `1000` (fully opaque).
- `tw`/`th` (`target_width`/`target_height`) are **garbage**: `tw=158239601`
  (should be `3840`), and `th=3840` (should be `2160` — i.e. `th` reads what
  `tw` should have been, the classic one-slot-shift signature seen in the
  sibling `FramebufferDriver`/`TaskbarModel` bug).
- Because `tw`/`th` are wrong, `size_matches` (`embedding_width ==
  target_width and embedding_height == target_height`) is always `false`, so
  `fills_target_exactly` is always `false` for this batch, even though the
  embedding genuinely fills the target exactly.

## Location

`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`, inside
`_engine2d_draw_ir_render_batch_embedded`:

```
649:    val target_width: i32 = eng.width()
650:    val target_height: i32 = eng.height()
...
657:    val size_matches = embedding_width == target_width and embedding_height == target_height
658:    val fully_opaque = embedding_opacity >= 1000
659:    val fills_target_exactly = origin_matches and size_matches and fully_opaque
...
679:    val use_embedded_surface = embedding.surface_id != "" and depth < ENGINE2D_DRAW_IR_EMBED_MAX_DEPTH and embedding.width > 0 and embedding.height > 0 and not fills_target_exactly and (needs_real_offscreen or (not embedding.clip and not baremetal_direct))
680:    _engine2d_route_dbg("[route-dbg] sid={embedding.surface_id} ew={embedding_width} eh={embedding_height} tw={target_width} th={target_height} op={embedding_opacity} clip={embedding.clip} bd={baremetal_direct} fte={fills_target_exactly} ues={use_embedded_surface}")
```

`eng.width()`/`eng.height()` are thin accessors on `Engine2D`
(`src/lib/gc_async_mut/gpu/engine2d/engine.spl:754-758`):

```
754:    me width() -> i32:
755:        self.w
756:
757:    me height() -> i32:
758:        self.h
```

So the actual misread is on `Engine2D.w`/`Engine2D.h` (or whichever fields the
cross-module ambiguous-name scan substitutes for them), read from
`draw_ir_adv.spl` — a different module than `engine.spl`. `w`/`h` (and the
synonyms `width`/`height`) are extremely common field names across the OS/UI
struct graph (the sibling bug counted 801 declarations of `width` alone at
whole-program scale), which is exactly the shape the sibling bug's
receiver-blind ambiguous-field-index scan mis-resolves.

## Root cause (hypothesis)

Same mechanism as the pinned root cause in
`simpleos_native_build_framebufferdriver_crossmodule_field_offset_shift_2026-07-14.md`
§ "2026-07-14 — Linux-host team follow-up": the Rust seed's HIR lowering
(`src/compiler_rust/compiler/src/hir/lower/type_resolver.rs:155,548-625`)
registers an imported struct's fields as `TypeId::ANY`, then resolves a field
NAME to an INDEX via a receiver-blind "struct declaring the most fields with
this name wins" scan — at whole-program scale this picks the wrong struct's
field order for `Engine2D.w`/`.h` when `eng` crosses the
`engine.spl` -> `draw_ir_adv.spl` module boundary. The
`try_resolve_receiver_struct_name_from_expr` /
`try_resolve_global_field_index_by_name` disambiguation added for the
`FramebufferDriver` case (`src/compiler_rust/compiler/src/hir/lower/expr/access.rs`)
is the same fix shape but has not been verified against this call site — it
was captured as an uncommitted patch
(`scratchpad/screendump_handoff/compiler_field_fix.patch`) as of the sibling
bug's 2026-07-16 entry and this document does not confirm whether it has since
landed and covers `Engine2D.width()/height()`.

## Why harmless today / when it would bite

Today the desktop's full-page batches are `baremetal_direct` (opaque AND
`backend_name() == "baremetal"`, `draw_ir_adv.spl:678`), which forces
`use_embedded_surface = false` regardless of `fills_target_exactly`
(`draw_ir_adv.spl:679`), so the batch always paints directly onto the parent
engine and the wrong `fills_target_exactly` value is never consulted for
routing. It still affects two secondary reads gated on
`fills_target_exactly`: `apply_clip` (`draw_ir_adv.spl:682`, only relevant
when `embedding.clip` is also true — not the case for the desktop batch today)
and `blend_images` (`draw_ir_adv.spl:685`, only relevant when
`embedding.surface_id != ""` — also not the case for the desktop batch today).

It would start mattering if:
- a translucent (`opacity_milli < 1000`) full-page batch needed the
  `fills_target_exactly` fast path (`needs_real_offscreen` would then be true,
  defeating `baremetal_direct`'s override at `draw_ir_adv.spl:679`), or
- a non-baremetal backend (vulkan/metal/software/cpu) rendered a full-page
  batch, since `baremetal_direct` is baremetal-only — those backends have no
  equivalent override and would always take the (unnecessary) embedded-surface
  path for a batch that should have hit the direct fast path, at minimum
  wasting a full offscreen alloc/blend per frame.

## Fix options

1. **Thread trusted scalar dims into the function (pure-Simple, preferred —
   mirrors the `fb_w`/`fb_h` trusted-scalar precedent in
   `engine2d_wm_frame_executor.spl` from the sibling bug's "Partial workaround
   applied" section).** Pass the screen/target width and height in from a
   caller that already has them correctly (e.g. the values used to construct
   the `Engine2D`/`FramebufferDriver` in the first place) instead of reading
   them back via `eng.width()/eng.height()` across the module boundary.
2. **Compiler-side fix**: verify/land the `access.rs`
   `try_resolve_receiver_struct_name_from_expr` disambiguation patch against
   this exact call site (`eng.width()`/`eng.height()` inside
   `_engine2d_draw_ir_render_batch_embedded`) the same way it was verified for
   `FramebufferDriver.width`/`.height` — this is the durable fix and would
   close both bugs (and any other instance of the same class) at once.

## Reproduction

Flip `ENGINE2D_DRAW_IR_ROUTE_DBG` to `true` in
`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:38`, rebuild the SimpleOS
x86_64 kernel per the recipe in
`doc/07_guide/os/baremetal/baremetal_simple_codegen_landmines.md` §
"Verification recipe", boot under real OVMF/QEMU, and grep the serial log for
`[route-dbg]`. Compare `tw`/`th` against the known-correct `ew`/`eh` on the
full-page desktop batch — `ew`/`eh` are the reliable oracle since they come
from the same `DrawIrEmbeddingConfig` struct's `width`/`height` fields and
read correctly at this call site. Revert the flag to `false` before landing
(budget-capped serial probe, log-retention policy: keep the probe, gate it
off — see `draw_ir_adv.spl:25-36` for the existing rationale comment).
