# Engine2D Font Offload Feature Expert

## Role

Own feature-specific process knowledge for Engine2D's **configured-font
execution** lane: how a `FontRenderConfig` picks a backend, how the attempt
ledger is built, and which routing invariants are load-bearing. This is the
routing layer — glyph outline decode and rasterization belong to
[vector fonts](../vector_fonts/skill.md).

The recurring failure mode here is not a wrong pixel; it is a **silently empty**
one: a backend that is attached but has no framebuffer accepts every dispatch,
returns empty readback, and reports nothing wrong. This entry keeps the
distinguishing rules in one place.

## Pipeline Links

- [verify skill](../../../../.claude/skills/verify/SKILL.md)
- [impl skill](../../../../.claude/skills/impl/SKILL.md)

## Feature Links

- Routing + ledger: [src/lib/gc_async_mut/gpu/engine2d/engine.spl](../../../../src/lib/gc_async_mut/gpu/engine2d/engine.spl)
  (`_vulkan_primitive_target` L409-439, `_draw_font_batch_staged` L1607-1720,
  `font_execution_attempts` L344).
- Preference order + alias folding: [src/lib/nogc_async_mut/gpu/engine2d/backend_lane.spl](../../../../src/lib/nogc_async_mut/gpu/engine2d/backend_lane.spl)
  (`_engine2d_backend_canonical_name` L86, `engine2d_backend_lane_full_preference_order` L80).
- Guide: [doc/07_guide/ui/engine2d_font_offload_fallback.md](../../../07_guide/ui/engine2d_font_offload_fallback.md)

## Rules that have already cost a bug

**1. Primitive routing and font offload are different mechanisms.** Primitive
routing is a five-arm chain that picks *one* backend. Font offload *tries* each
candidate and judges it by whether it consumed the batch
(`quad_index == batch.quads.len()`). Do not reason about one from the other.

**2. Only Vulkan needs an `.initialized` guard, and there is a reason.** It is
the only arm where `self.backend` can diverge from a non-nil sibling field —
`_poison_vulkan_font_surface` (L391) swaps `self.backend` deliberately, and
tests attach a bare `VulkanBackend.create()`. The virtio-gpu and baremetal
create paths pass the *same object* as both `backend:` and the sibling field;
the cuda arm is gated on `selected_backend_name`, set only where `init()`
already succeeded. Before adding a guard to another arm, prove the divergence is
reachable from a real construction path — as of 2026-08-16 it is not.

**3. Do not replace that guard with `backend_probe_initialized`.** It takes a
`BackendProbeResult`, not a backend instance; `VulkanBackend.initialized` is a
plain `bool` field. The substitution does not compile. The import at
`engine.spl:57` serves the strict-create paths.

**4. The preference order is all-lowercase, and canonicalization depends on it.**
`_engine2d_backend_canonical_name` does `.trim().lower()` before folding
aliases. A capitalized entry in the order list silently stops matching.

**5. A ledger that does not end in a success entry means the batch was dropped**,
not offloaded elsewhere. `cpu:success` is the documented last resort.

## Known open items

- **rocm `self.backend` hijack.** `engine.spl` L1700-1701, L1941-1942,
  L2006-2007 do `if rocm.initialized: self.backend = rocm` on an engine whose
  `selected_backend_name` is something else; the cuda arm gates on the name
  instead. Asymmetric, currently unreachable, recorded not patched.

## Verification

| Level | Spec | Status |
|---|---|---|
| Unit, in-process | `test/01_unit/lib/gpu/engine2d/font_runtime_config_spec.spl` | live |
| Unit, uninitialized Vulkan | `test/01_unit/lib/gc_async_mut/gpu/engine2d/engine_vulkan_font_route_spec.spl:73-92` | live |
| System, native binary | `test/03_system/lib/gpu/engine2d/engine2d_font_offload_fallback_system_spec.spl` | **fail-closed, unexecuted** |

The system lane requires an admitted pure-Simple runtime
(`SIMPLE_QUALIFIED_RUNTIME`) and **fails rather than skips** without one. As of
2026-08-16 no such runtime exists on the reference machine — see
[the lane plan](../../../03_plan/sys_test/engine2d_font_offload_fallback_system_lane.md)
and `.spipe/stage3-segfault-fix/`.

**Never accept Rust-seed output as evidence for this feature.** The seed
self-identifies in its `--version` banner; the admission gate rejects it.

## Lane History

- 2026-08-16 — `b10f1b4309c` reviewed and found sound. It repairs a call to
  `backend_canonical_name`, a symbol defined and imported **nowhere** in
  `backend_lane.spl` (that file has no `use` lines at all), so the old L129 call
  site could never have resolved. Route audit concluded the `.initialized` guard
  needs no sibling changes. Lane state:
  `.spipe/restart12_engine2d_font_seed_review/state.md`.

## Metal reached Vulkan's font batching — 2026-09-05

Metal's font composite now has the same shape Vulkan has carried since
2026-08-12. Read this before touching either backend's font path, because the
two are now deliberately twins and a change to one without the other is a
divergence, not an improvement.

The shared frozen contract:

| Piece | Vulkan | Metal |
|---|---|---|
| Packed shader | `font_atlas_composite_vulkan_glsl_source` | `font_atlas_composite_metal_packed_source` |
| Packer | `vulkan_font_packed_params` -> `[u8]` | `metal_font_packed_params` -> `[u32]` |
| Frame contract | `vulkan_font_frame_batch_contract` | `metal_font_frame_batch_contract` |
| Warm reuse | `font_params_pool` / `font_descriptor_pool` | `packed_pool` |
| Flush | `_flush_pending_compute` | `MetalFontBackendState.flush` |

Word layout is frozen and identical on both: 8 header words
(atlas_w, atlas_h, atlas_count, dst_w, dst_h, dst_count, glyph_count,
max_pixels), then 7 words per glyph (atlas_x, atlas_y, w, h, dst_x, dst_y,
color). `max_pixels` at word 7 is host-side only — it is the dispatch width;
no shader reads it. The glyph cap is 4096 on both.

Traps this cost time:

- **A single shared packed buffer is wrong.** Batch N+1 overwrites it before
  batch N's dispatch runs. Both backends pool one buffer per pending batch and
  reset the pool index on flush.
- **MSL has no `buffer.length()`.** The GLSL gets its bounds checks free from
  `p.words.length()`; the MSL binds the word count at buffer(3) to get the
  same guarantee. Do not drop that binding as "redundant" — it is the only
  thing bounding a GPU-side read if the packer is ever wrong.
- **Deferring text means ordering is yours to keep.** Metal's primitives still
  submit immediately, each from its own command buffer, so `font.flush()` runs
  at all six of those sites plus readback, present and `submit_batch`. Adding a
  seventh immediate command-buffer site without a flush silently paints the
  frame out of order.
- **`begin_frame` must be wired or the contract is meaningless.** It resets the
  per-frame counters at `clear()`, after the previous frame's flush. Without
  that call the counters accumulate and `frame_batch_contract_met` is false
  from frame 2 on.
- **The completion latch cascades by design.** A failed dispatch sets
  `completion_unknown` and every later draw early-returns, exactly like the
  Vulkan/MoltenVK behavior in
  `doc/08_tracking/bug/vulkan_engine2d_sequential_frames_flaky_moltenvk_2026-09-02.md`.
  Only encode and dispatch failure set it; allocation failures do not.

## Verification, Metal packed lane

| Level | Spec | Status |
|---|---|---|
| Unit, no device | `test/01_unit/lib/gc_async_mut/gpu/engine2d/metal_font_packed_parity_spec.spl` | live, 5/5 |

That spec proves layout parity with Vulkan byte for byte, shared constants and
dispatch arithmetic, and the one-command/one-commit/one-wait frame contract.
**It does not prove device execution.** No Metal-featured binary exists on the
reference machine, so the packed path's real speedup is unmeasured and the 21x
figure in `doc/01_research/local/metal_2d_frame_cost_perf.md` predates it.

DirectX gets none of this and cannot until it has a GPU text path at all —
both its text entrypoints delegate to the software mirror. Scope recorded in
`doc/08_tracking/bug/directx_2d_has_no_gpu_text_path_2026-09-05.md`.
