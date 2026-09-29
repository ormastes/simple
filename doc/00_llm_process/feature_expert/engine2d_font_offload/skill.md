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

**Instantiation from `engine.spl` is REACHABLE — resolved 2026-09-05.**
An earlier revision of this file said the opposite; it was wrong and is
corrected here. `backend_metal_font_spec`'s "wires the typed Metal font backend
only into native Metal constructors" scenario asserted the literal string
`metal_backend: metal, w: width`, which appears nowhere in `engine.spl` and
never did. The spec was stale, not the wiring. The real construction path:
`create_with_backend_fast`, `create_requested_backend` and
`create_shared_metal_surface` each call `MetalBackend.create()` and then write
`metal_backend: Some(metal), opencl_backend: nil,` (three occurrences), and
`MetalBackend.create()` sets the typed `font: MetalFontBackendState` field
itself. So the Metal font path is constructed every time a native metal backend
is created. The `"metal-on-vulkan"` compatibility lane uses `VulkanBackend` and
never sets `metal_backend`, which is why the spec's second assertion was always
correct. The stale assertion now names the actual fragment and passes.

What remains unproven is narrower and still true: **no Metal device has
executed the packed path.** The parity spec proves the packer and the frame
contract without a device, and this host has no Metal-featured binary. Do not
read a green parity run as evidence the GPU produced correct pixels.

## Atlas continuity is PER OWNER, not per global generation (2026-09-12, F22)

`FontRenderBatch.atlas_generation` is one **global** counter, bumped by every
atlas owner. Any backend rule of the form `batch.atlas_generation ==
host_generation + 1` therefore cannot hold on a page where two font identities
interleave, and forces a full 1,048,576-pixel repack per switch. Use
`FontRenderBatch.atlas_owner_sequence` (added in `font_types.spl`) instead; the
decision itself lives in the device-free free function
`vulkan_font_mirror_continuity` (`backend_vulkan_helpers.spl`), which returns
FULL / INCREMENTAL / **ALREADY_TRUTH** — the last for a returning owner whose
glyphs are all cached, which emits no dirty cells and whose mirror is already
exact.

**The trap that makes the sequence alone unsound:** `Engine2D` keeps ONE
`FontRenderer` and ONE atlas, and a face switch used to `_reset_font_atlas`,
i.e. WIPE it. A per-owner sequence without the matching producer-side park lets
`can_increment` fire against a mirror holding the owner's pre-wipe pixels while
the truth is a freshly re-rasterised atlas — `SIMPLE_VK_FONT_SELFCHECK=1` goes
red. The two halves must land together: `FontAtlasPark` + `_switch_font_atlas`
in `font_renderer.spl`, and the sequence in `font_types.spl`.

Second trap: several staging paths insert a glyph and then abort with
`valid: false` before the `dirty.len() > 0` bump, so the atlas can move without
the sequence moving. `atlas_unpublished_mutation` makes `_stage_batch` publish
`-1` (no continuity claim) until a dirty batch names the cells.

Controls: `SIMPLE_FONT_ATLAS_PARK=0` (producer park off),
`SIMPLE_VK_FONT_PER_OWNER_MIRROR=0` (consumer mirrors off). Record:
`doc/08_tracking/bug/vulkan_font_atlas_shared_mirror_repacks_2026-09-12.md`.
