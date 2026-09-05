# SimpleOS Vulkan Render Backend Plan (lane G0)

Status: architecture/plan only. No Vulkan calls are implemented by this doc.
Lane G0 of `doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md` §6
("GPU plan + backends", lines 283-320). This is the "common GPU plan" that G1
(Vulkan), G2 (Metal), G3 (D3D12) all sit behind.

Related, not duplicated: `doc/03_plan/os/simpleos/screens_showcase_2d_opt_plan.md`
Workstream E (virtio-gpu/Venus transport bring-up) and
`.spipe/simpleos-screens-render-lane/state.md` (WS-E status, AC-9). This doc is
the render-pipeline-side architecture that Workstream E's transport plugs into;
it does not restate E's opcode/capset bring-up steps.

## 1. Frame path: scene → GpuRenderPlan → virtio-gpu/venus command stream

The redesign plan already specifies the backend-agnostic intermediate:
`GpuRenderPlan {passes, batches, uploads, transients, capability_key}`
(`render_perf_redesign_plan_2026-08-06.md:285-286`). The common optimizer
(instancing, batching, dirty-range uploads, transient lifetimes, residency)
produces this plan from the existing unified packed DrawIR-v3 scene arena
(landed L0-L9, see MEMORY `project` note; one arena, no separate GUI/Web
display lists). **Backends only encode** — they must not re-decide what to
draw, only how to submit it.

For the Vulkan/venus backend specifically, encoding a `GpuRenderPlan` means:

1. **Session setup (once, not per frame).** `CTX_CREATE` with
   `context_init` carrying the Venus capset id in its low 8 bits
   (`virtio_gpu.h:283-284`, cited in
   `doc/01_research/os/vulkan/venus_virtio_gpu_protocol_facts.md` §3). The
   capset id itself must be **discovered** via `GET_CAPSET_INFO` enumeration,
   never hardcoded — the protocol-facts doc rates `CAPSET_VENUS = 4` as
   MEDIUM/recollection-only, not present in the uapi header (§2, §8.2).
2. **Ring bring-up (once).** `RESOURCE_CREATE_BLOB` with `BLOB_MEM_HOST3D`
   (not `BLOB_MEM_GUEST` — the protocol-facts doc calls guest-only memory "not
   a valid minimum-viable path... a dead end" for Venus, §8.3) +
   `USE_MAPPABLE`, then `RESOURCE_MAP_BLOB` against shmid **1**
   (`VIRTIO_GPU_SHM_ID_HOST_VISIBLE`, `virtio_gpu.h:127`), then a `SUBMIT_3D`
   carrying a guest-authored `vkCreateRingMESA` command. The exact wire
   encoding of that command is explicitly **LOW confidence / not sourced in
   this tree** (§5, §9) — G1 must fetch Mesa's
   `venus-protocol/vn_protocol_driver_transport.h` before implementing this,
   not derive it from the facts doc.
3. **Per-frame submission.** Each `GpuRenderPlan` batch becomes one or more
   Vulkan commands serialized into the ring, sent via `SUBMIT_3D`
   (`0x0207`, hdr + `le32 size` + `le32 padding` = 32B header,
   `virtio_gpu.h:305`). Fencing must set both `VIRTIO_GPU_FLAG_FENCE` and
   `VIRTIO_GPU_FLAG_INFO_RING_IDX` with `hdr.ring_idx` set to the Venus ring
   used — the facts doc flags the *plan's own* E2.5 draft as defective for
   setting only `FLAG_FENCE`, which silently fences ring 0 regardless of
   where the work went (§5, bullet on "plan defect"). G0/G1 must not repeat
   that mistake: `ring_idx` is a real header field
   (`virtio_gpu_ctrl_hdr`, `virtio_gpu.h:137`), not padding.
4. **Present.** Scanout via `SET_SCANOUT_BLOB` (`0x010d`) against the
   swapchain-equivalent image, matching the existing `CompositorBackend`
   `present()`/`present_rect()` contract (see §3).

## 2. Vulkan surface actually needed: 2D compositing, not a 3D engine

This is a 2D scene compositor, not a rasterizer for arbitrary 3D geometry.
The Vulkan surface the backend needs is deliberately narrow:

- **Fixed small pipeline set**, not a general PSO cache with user shaders:
  one blit/copy pipeline, one solid-fill pipeline, one src-over blend
  pipeline (mirrors the CPU-side operation set already enumerated in
  `kernel_registry.spl:35-39`: `FILL_CONST`, `COPY_SPAN`, `SRC_OVER_CONST`,
  `SRC_OVER_IMAGE`, `MASK_SRC_OVER`), plus a text/glyph-mask blend variant.
  No arbitrary vertex/fragment shader compilation path, no depth buffer, no
  3D transform pipeline.
- **Image-based compositing**: source images/atlases as sampled images,
  destination as a storage/color-attachment image, blended per the *same*
  Porter-Duff src-over formula already codified as the authoritative oracle
  in `scalar_oracle.spl:38-59` (`oracle_src_over`, ARGB straight-alpha,
  premultiplied compositing, floor-truncating division). The GPU kernel is
  not free to pick a different blend formula — it is graded against that
  oracle (§3 below).
- **Persistent session state**, per the redesign plan's backend-session
  model (`render_perf_redesign_plan_2026-08-06.md:289-292`): device/queue,
  2-3 frame contexts, upload rings, one small pipeline cache, one
  descriptor/argument allocator, atlas images, a transient heap, and
  fence/timeline sync objects — created once, never recreated per frame.
  Warm frames never allocate a full framebuffer, wait-idle, or read back.
- **Upload path precedent**: `src/runtime/runtime_rocm.c:513-529`
  (`rocm_engine2d_copy_to_device` / `rt_engine2d_rocm_upload_pixels`) shows
  the pattern this repo already uses for a different GPU backend (ROCm/HIP):
  build one packed `uint32_t[]` host buffer, one `hipMemcpy` H2D call, no
  per-pixel or per-row FFI crossings. The Vulkan/venus backend should follow
  the same shape — one packed pixel buffer per dirty region, uploaded through
  the blob-backed staging ring described in §1, not a per-row copy. This is
  precedent for the *packing discipline*, not a venus-specific detail; ROCm
  and venus are unrelated transports.

## 3. Integration with kernel_registry's gating contract

`kernel_registry.spl` already encodes the selection rule this backend must
obey: a candidate provider is registered into a slot **only if `bit_exact`
AND `faster`** (`kernel_table_register`, lines 127-149) — both required
independently, because CPU-SIMD in this same tree already failed exactly
this test (8K full-fixture: SIMD 1282.2ms slower than scalar 909.5ms,
`render_perf_diagnosis_2026-08-06.md` claim 1, VERIFIED). The GPU/Vulkan
backend is **not exempt** from this: it is registered as `KERNEL_PROVIDER_*`
value greater than `KERNEL_PROVIDER_SCALAR` (0), keyed on the same
`(op, format, alignment, contiguity, bucket)` axes
(`kernel_slot_key`, lines 81-99), and only claims a slot when:

1. **Bit-exact** — its ARGB output for every op matches `scalar_oracle.spl`'s
   `oracle_*` functions pixel-for-pixel, including the floor-division and
   the `sa==0`/`sa==255` fast-path behavior (`oracle_src_over`, lines
   38-59). A GPU blend implemented with a rounding or premultiplication
   convention that differs even slightly fails this gate and the slot stays
   on scalar — silently, by design (`kernel_table_lookup` returns
   `KERNEL_PROVIDER_SCALAR` for anything unregistered, line 157-163).
2. **Faster** — measured against the current CPU provider in that exact
   slot (which may itself be scalar or a registered SIMD provider), not
   against a generic "GPU is fast" assumption. Given claim 1's precedent
   (a CPU vector path that lost to scalar), a GPU path must clear this bar
   with a real benchmark before it ships, not on the strength of "it's the
   GPU."
3. Registration happens **once per session** before `kernel_table_seal`
   (line 152-155); the frame path never re-probes device capability.

Practically: the Vulkan backend is a `KERNEL_PROVIDER_VULKAN` id registered
per-slot the same way a new SIMD ISA would be — this doc does not propose a
parallel/bypass selection mechanism. Large, GPU-favorable ops (full-screen
blur, scale, video-sized blits — see `render_perf_diagnosis_2026-08-06.md`
line 70, "full-screen blur/scale/video belongs on the GPU") are the
plausible first slots to clear the bit-exact+faster bar; small/tiny spans
almost certainly do not (upload latency alone likely loses to scalar for a
16-pixel fill) and should not be force-registered.

## 4. HARDWARE REALITY (board-runnable rule)

Per `.claude/rules/board-runnable.md`: QEMU is a dev harness, the board is
the target, and a QEMU-only result is a defect, not a completion. State of
this lane:

- **What "runs" today**: nothing yet — G0 is architecture only. The
  transport this plan describes (virtio-gpu 3D + Venus over `SUBMIT_3D`)
  is fundamentally a **virtio device**, i.e. paravirtualized. It exists
  because a VM guest has no direct GPU, not because it is a
  hardware-portable abstraction.
- **QEMU status is itself blocked on this host**: the protocol-facts doc
  records that `qemu-system-x86_64 -device virtio-gpu-gl-pci,help` fails to
  load (`hw-display-virtio-gpu-gl.so: undefined symbol: qemu_egl_display`)
  on the host it was written on (§9). So even the QEMU side of this plan is
  currently unverified as runnable, not just the board side.
- **Board path: not merely unimplemented, structurally different.** virtio-gpu
  is a VM device interface; a physical SimpleOS board has no virtio-gpu
  device to talk to at all. Reaching real hardware requires an entirely
  separate driver (a native GPU/display driver talking directly to silicon,
  or whatever the board's actual GPU/display IP is), not a "finish the venus
  work and it'll run on the board" continuation. This plan does not invent
  that story. Both `screens_showcase_2d_opt_plan.md` Workstream E4 and
  `.spipe/simpleos-screens-render-lane/state.md` (lines 178, "Physical-board
  GPU display evidence... gap filed per...") already flag this as a gap
  requiring separate tracking; this doc does not duplicate that filing, it
  reaffirms the same gap applies to G0-G4.
- **Action**: the QEMU-vs-board split must remain visible in every gate this
  lane produces (mirrors the `cpu_selected`/`gpu_fallback` receipt pattern
  at `draw_ir_v3_execution_route.spl:7-18`) — a Vulkan/venus capability
  claim must carry a `"qemu_only"` scope marker and must not be read as
  "GPU rendering works on SimpleOS" without qualification.

## 5. Verified vs Unverified

**Verified (file:line read in this tree):**
- Venus capset carries no ring layout; ring geometry is guest-authored via
  `vkCreateRingMESA` over `SUBMIT_3D` —
  `doc/01_research/os/vulkan/venus_virtio_gpu_protocol_facts.md` "Headline
  finding".
- `virtio_gpu_ctrl_hdr` = 24B incl. real `ring_idx` field — same doc §2,
  citing `virtio_gpu.h:137`.
- `CTX_CREATE`/blob create/map struct layouts and opcodes — same doc §3-4,
  cited to `virtio_gpu.h` line numbers.
- `VIRTIO_GPU_SHM_ID_HOST_VISIBLE = 1` — same doc §4, `virtio_gpu.h:127`.
- `FLAG_FENCE`/`FLAG_INFO_RING_IDX`/`ring_idx` semantics, and that the
  plan's own E2.5 draft under-sets them — same doc §5.
- `src/lib/nogc_async_mut/gpu/vulkan_icd_virtio.spl:42-46` defines
  fabricated stub opcodes, not real Venus — same doc §6, do not treat as
  reference.
- `kernel_table_register` requires bit-exact AND faster, rejects otherwise —
  `src/lib/common/gpu/engine2d/kernel_registry.spl:127-149`.
- `oracle_src_over` blend formula (Porter-Duff src-over, straight alpha,
  floor division, `sa==0`/`255` fast paths) —
  `src/lib/common/gpu/engine2d/scalar_oracle.spl:38-59`.
- CPU-SIMD measured slower than scalar at 8K (1282.2ms vs 909.5ms) —
  `doc/01_research/ui/perf/render_perf_diagnosis_2026-08-06.md` claim 1,
  VERIFIED, citing `gui_perf_benchmark_comparison.md:53-54`.
- `RenderBackend` trait (`src/lib/common/ui/backend.spl:32-55`) and
  `CompositorBackend`/`CompositorGlassCapable` traits
  (`src/os/compositor/display_backend_core.spl:1-17`) are the existing
  abstractions this backend must implement — no new trait is proposed here.
- ROCm packed-upload precedent —
  `src/runtime/runtime_rocm.c:513-529` (`rocm_engine2d_copy_to_device`).
- `GpuRenderPlan` shape and per-backend session model —
  `doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md:285-292`.
- Local QEMU cannot currently load `virtio-gpu-gl` on the host the
  protocol-facts doc was written on — same doc §9.

**Unverified / open (flagged, not fabricated):**
- The actual numeric Venus capset id (recollection-rated MEDIUM, "do not
  hardcode" — protocol-facts doc §2, §7).
- The exact `vkCreateRingMESA` wire encoding — rated LOW, "do not implement
  from this document" (same doc §5, §9).
- Whether QEMU on any host in this repo's CI/dev fleet currently accepts
  `context_init=true` / can load `virtio-gpu-gl` at all — rated LOW/unverified
  (same doc §9); this doc's HARDWARE REALITY section treats even the QEMU
  side as unproven until re-checked on a working host.
- Physical-board GPU/display driver path: not merely unverified but
  out-of-scope for virtio-gpu entirely (see §4) — needs its own tracked gap,
  not assumed to be a downstream step of this plan.
- Which `GpuRenderPlan` batches will actually clear the kernel_registry
  bit-exact+faster bar: no GPU benchmark exists yet in this tree; §3's
  "large ops are plausible first candidates" is a prediction, not a
  measurement.

## 6. Non-goals for G0

- No Vulkan/venus calls are implemented here (deferred to G1).
- No new backend trait — reuse `RenderBackend` (`backend.spl`) and
  `CompositorBackend` (`display_backend_core.spl`) as-is.
- No attempt to make virtio-gpu/venus "board-runnable" by construction — per
  §4, that is a distinct driver problem, tracked separately, not solved by
  finishing G1-G4.
