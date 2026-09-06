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

## 2026-09-06 — GPU/2D honesty sweep (Vulkan / Metal / DirectX)

All `file:line` read at `origin/main` `461e48379ff`. PRs #410 and #422 were both
**OPEN** on this date — read every "fixed" below as "fixed on an unmerged branch",
not as a property of `main`.

**Vulkan is genuinely real, and unusually honest about it.** Readback provenance
discriminates five distinct states, all five literals emitted in one readback
body — `completion_unknown` (`backend_vulkan.spl:1468`, `:1482`),
`readback_failed` (`:1494`, `:1510`), `cpu_fallback` (`:1496`, `:1512`),
`device_readback` (`:1498`), `host_cache_after_device_copy` (`:1519`). Backed by
a sticky `cpu_fallback_used` field (`:293`) and a `completion_unknown` field
(`:295`) that gate the device-purity predicates at `:411-412` and `:430`. Shutdown quarantines on `completion_unknown` instead of
freeing in-flight resources. Use this backend as the reference for what an honest
provenance ladder looks like; the other two are measured against it.

**Three fakes found and fixed on PR #410:**
1. `backend_directx.spl:444,452` returned `source = "device_readback"` with a
   positive handle for pixels the CPU rasterized — over an ICD whose own docstring
   says queue submit/present are "pending rt_dlopen for real libvulkan"
   (`nogc_async_mut/gpu/vulkan_icd_sffi.spl:204,218`). A spec *pinned* the fake.
2. `session/backend_vulkan_adapter.spl:24 init_device()` could report success
   through unbacked externs (silent nil). The whole layer is now deleted — see
   `doc/08_tracking/bug/gpu_session_layer_orphan_deleted_2026-09-06.md`.
3. `MetalFontBackendState.frame_batch_contract_met()`
   (`backend_metal_font.spl:162`) had **zero callers** — the one method that would
   read the counters a real frame produced was dead code, while the parity spec
   asserted the contract over hand-fed literals. **Measured on committed content,
   not assumed:** `grep -c` gives **0** at `origin/main` `461e48379ff` and **2**
   at #410 head `a5990b23ed2` (`backend_metal.spl:815`, `:821`), which also adds
   the caller spec `backend_metal_device_free_contract_spec.spl:77,89,101`. So it
   is fixed **on #410 only**, still unmerged. Anything you see in the shared jj
   WC is uncommitted peer work — verify against a committed ref before citing.

**Hazard class: self-mocking specs.** The pre-rewrite copies at
`test/unit/gpu/{graphics_session,session_mode_separation,backend_session_sharing}_spec.spl`
imported only `std.io` / `std.spec` and then defined their **own** local
`GraphicsSession`, `Caps`, `SessionHandle`, `SessionPolicy` classes. They could
not fail, because they tested nothing that ships. This is worth grepping for as a
class: a spec whose `use` lines name no product module, or that declares a class
with the same name as the subject, is vacuous by construction.

**Correction — "Vulkan `draw_text` never reaches the atlas" was too broad.**
`Engine2D.draw_text` (`engine.spl`) already routes TTF/vector text into the
Vulkan font atlas: `draw_text` -> `has_sffi_ttf` -> `draw_text_configured` ->
`stage_text_configured` -> `_draw_font_batch_staged` -> `_draw_font_batch_plan`
-> `composite_font_batch`. Only the built-in **5x7 bitmap** path lacked an atlas
lane (`backend_vulkan.spl` `me draw_text`, CPU `text_blit_buffer` then
`draw_image_blend`) — that is what PR #422 adds, reusing the frozen composite
SPIR-V; no new shader.

**No Metal device evidence exists on this machine. None.**
`build/test-macos-metal-render-log-pass/capture.env` is a hand-written **spec
fixture**: the literal `macos_metal_gpu_capture_artifact_magic=XCODE-GPUTRACE`,
sitting beside `-fail`, `-bad-capture-magic`, `-missing-inputs` and six other
fixture dirs. `doc/08_tracking/test/test_result.md` records both Metal perf specs
as `unknown` — never a pass. Read every green Metal run as "the device-free
contract holds", never as "the GPU produced correct pixels".

**Two unpinned Vulkan session seams (`engine2d/vulkan_session.spl`):**
- `create_command_buffer()` `:315-321` calls `vulkan_sffi_begin_compute()` with
  **no session/initialized guard**, so it can hand back a handle on an engine
  with no device — a false oracle for anything that treats a non-zero return as
  proof of a session.
- `_cleanup()` `:486` zeroes `command_pool`/`pipeline_cache`/`allocator`
  `:547-549` with no destroy call. Read the nuance before filing a leak: those
  three fields are declared "runtime-managed placeholder" `:78-80` and are
  initialised to 0 `:131-133`, so the zeroing is *vacuous*, not a leak. The real
  finding is that the fields exist and nothing owns them.

**Deferred, recorded, not faked** (both keep their `# TODO:` markers — deferred
is not done, never convert to NOTE):
- GPU **glyph rasterization** (outline -> coverage) on Vulkan and Metal:
  `doc/08_tracking/bug/gpu_glyph_rasterization_gpu_deferred_no_device_2026-09-06.md`.
  Note the distinction that keeps being lost: the atlas blit is a **lookup**, not
  a raster. Bitmap raster already exists on the generated-kernel lane
  (`cuda_session.spl:394`, `opencl_session.spl:417`, `rocm_session.spl:242`
  `bitmap_glyph_raster_kernel`) and Metal blits bitmap glyphs on-GPU
  (`backend_metal.spl:708`, `:1914` `kernel_glyph_atlas_blit`).
- **DirectX GPU text**, both platforms: `backend_directx.spl:382-384` (`draw_text`)
  and `:221-223` (`draw_text_bg`) are `sw.draw_text*` + `_poison_native_receipt()`.
  `doc/08_tracking/bug/directx_gpu_text_deferred_no_windows_host_2026-09-06.md`.
