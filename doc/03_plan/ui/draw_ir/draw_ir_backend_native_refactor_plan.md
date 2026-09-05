# DrawIR Backend-Native Layout — Non-Destructive Refactoring Plan

Status: IN PROGRESS (2026-08-01). Stage state:
- S1 DONE `fe481ab069c` (enums file, formats u16→u32, de-magicked
  vulkan_backend3d, pre-FFI validation). Finding: runtime usage bits are
  RT-local, not VkImageUsageFlagBits — see arch doc §3.5.
- S2 DONE `31c858cab98` (accessor seam + MTL/DXGI/D3D12 remap tables + spec;
  DrawIrV3BlendParts made pub). Metal/DX backend WIRING deferred to S6 —
  their format values are engine-local, not DrawIR-canonical.
- S5 DONE `4755c8ab526` (gpu_web_capacity_strides.spl — additive, manifest
  API untouched).
- S0/spec execution DEFERRED: test runner hangs environment-wide (btrfs
  metadata 45.96/46.50 GiB, ENOSPC family); receipts in scratchpad only.
  Run draw_ir_v3_backend_{enums,access}_spec.spl +
  gpu_web_capacity_strides_spec.spl + draw_ir_v3_spec.spl first thing after
  runner recovery, BEFORE building on S1-S5.
- S3/S4 PARKED: need new externs → bootstrap rebuild; do not start until the
  filesystem is healthy and a rebuild window is scheduled.

Architecture:
`doc/04_architecture/ui/rendering/draw_ir_backend_native_layout.md`.
TLDR: `draw_ir_backend_native_refactor_plan_tldr.md`.

## Cross-reference (2026-08-05)

Orthogonal to, and not reversed by,
`doc/05_design/ui/unified_packed_ui_scene.md` (decision record §0): that
design's ONE physical DrawIR-v3 scene arena (decision 3) is the same arena
whose columns this plan makes Vulkan-canonical; S2's accessor seam and S5's
capacity-stride work sit beneath the design's L5 "session arena + native
writers" lane. Two v1/v2 axes here are distinct and must not be conflated:
- `draw_ir.spl` schema v2 (`DrawIrComposition`) — this plan's frozen CPU
  oracle, unrelated to the port axis below.
- `PackedDrawPort` (ports) v1 (`draw_ir_v3_ports.spl`, frozen, by-value
  submission) vs. v2 (`draw_ir_v3_ports_v2.spl`, new, by-reference
  `PackedSceneRef`) — design decision 6. S1 item 2 below ("any
  `PackedDrawPort` impl") touches only v1's existing readers/writers for the
  `formats` u16→u32 widening sweep; it does not create or edit v2.

Goal: v3 DrawIR columns carry Vulkan-canonical values and layouts so the
Vulkan lane consumes them with zero conversion (direct SFFI to libvulkan,
packed-record pointer pass); Metal/DX read the same data through remap
accessors; one-time allocation sizing becomes backend-stride-aware.

Non-destructive constraints (hold at EVERY stage):
- v2 (`draw_ir.spl`) untouched — frozen CPU oracle, SDN wire unchanged.
- v3 additive only, except the single enumerated widening in S1.
- Interpreter and native lanes both green after each stage; interpreter keeps
  scalar `rt_vulkan_*` externs throughout (dual-ABI switch, precedent
  `_vulkan_push_constants_abi`).
- Existing `rt_vulkan_*` surface is never removed in this plan — new lanes are
  added beside it and selected at session creation; removal is a follow-up
  once parity receipts exist.
- No silent fallback: any lane that can't honor a value rejects with a
  `DrawIrV3SubmitReceipt`, never degrades quietly.

## S0 — Freeze + baseline receipts (no code change)

- Record current behavior: run draw_ir v2/v3 spec suites + engine2d parity
  specs on both engines; store pass list as the regression bar.
- Verify the two standing bugs that gate correctness claims are respected in
  test choices (native Dict pitfalls; `simple test` delegating to seed —
  GREEN from `simple test` is not self-hosted evidence).
- Exit: baseline receipt checked into the lane state notes (not git-tracked
  reports unless requested).

## S1 — Name the numeric domains (additive + one widening)

Files: new `src/lib/common/ui/draw_ir_v3_backend_enums.spl`; touch
`draw_ir_v3.spl` (ResourceTable), `vulkan_backend3d.spl` (replace magics).

1. Add canonical constant sets, values = Vulkan verbatim:
   `DRAW_IR_FORMAT_* = VkFormat`, `DRAW_IR_BLEND_* = VkBlendFactor/VkBlendOp`
   (packed src|dst|op into u16 fields), `DRAW_IR_IMAGE_USAGE_* =
   VkImageUsageFlagBits`.
2. **Widen `ResourceTable.formats: [u16] → [u32]`** — u16 cannot hold VK
   extension formats (`1000156xxx`). v3 has no serializer; this is in-memory
   only. Enumerate and update every reader/writer in the same change
   (`draw_ir_v3.spl` accessors, `draw_ir_v3_emit.spl`, oracle, any
   `PackedDrawPort` impl). Sweep rule applies: enumerate the family, don't
   fix one site.
3. Replace magic numbers in `vulkan_backend3d.spl:73-78` and usage hexes
   (`0x43/0x23/0x12/0x35`) with the named constants — pure rename, values
   identical, zero behavior change.
4. Add range validation where Rust currently does `from_raw` unchecked:
   reject out-of-domain values with a receipt before the FFI call.
- Exit: S0 suite green; grep shows no bare format/usage literals left in
  backend .spl files.

## S2 — Accessor seam (Vulkan = identity, no wrapper)

Files: new `src/lib/common/ui/draw_ir_v3_backend_access.spl`; Metal/DX remap
tables live beside it.

1. Read accessors over Paint/Resource views: `*_vk()` are identity inline
   reads (the Vulkan lane may keep touching columns directly — the accessor
   exists for uniformity, not as a required hop); `*_mtl()` / `*_dxgi()` are
   static lookup tables (RGBA8: 37→70/28, BGRA8: 44→80/87, R8: 9→10/61,
   D32F: 126→252/40, plus blend tables).
2. Language reality: no setter dispatch exists in Simple — writes stay
   emit-kernel-only (already true in v3). Do NOT wait on a property-wrapper
   language feature; if wanted later, file it as a language feature request
   separately.
3. Metal (`backend_metal.spl`) and DX (`sffi_directx.spl` opcode builder)
   switch their format/blend translation to these tables — deletes their
   ad-hoc conversions without changing outputs.
- Exit: parity specs green on software/metal-sim/dx-emulation lanes; a
  table-driven spec asserts VK↔MTL↔DXGI rows against known constants.

## S3 — Packed Vk-record lane + direct SFFI to libvulkan (native only)

Files: new `src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan_direct.spl`;
touch `sffi_vulkan.spl` (lane switch), Rust runtime only for the loader
bootstrap export.

1. Record builders in Simple: exact byte images of `VkImageCreateInfo`
   (88 B: sType=14, pNext=0, ptr fields 0, SHARING_EXCLUSIVE),
   `VkImageViewCreateInfo`, `VkSamplerCreateInfo`, `VkBufferCreateInfo` —
   built once per resource into `[u8]`, passed as `rt_array_data_ptr_u8`.
2. Symbol resolution: bootstrap keeps the existing Rust lane for
   instance/device/queue creation; then `vkGetDeviceProcAddr` populates a
   direct-call table. Every resolved symbol is probed at session creation and
   **hard-fails** if missing — an unregistered `@extern fn` returns nil
   silently, so absence must be detected up front, never at draw time.
3. Dual-ABI: interpreter keeps `rt_vulkan_*` scalar externs; native selects
   the direct lane. New externs ⇒ bootstrap rebuild required — schedule with
   a planned rebuild window, do not bootstrap ad hoc.
4. Scope for this stage: resource creation calls only
   (image/view/sampler/buffer). Command recording stays on the existing lane.
- Exit: same rendered output (pixel-hash receipts) native lane vs S2
  baseline; created-resource handles interchangeable with Rust-lane handles.

## S4 — Batch submission + descriptor caching (the perf stage)

Files: `sffi_vulkan.spl`/`sffi_vulkan_direct.spl`, `backend_vulkan.spl`.

1. Kill per-primitive descriptor set + command buffer + fence + wait
   (`sffi_vulkan.spl:599-657`): persistent descriptor pool + cached sets keyed
   by (pipeline, resource-set), one command buffer per frame, one fence (or
   timeline semaphore) per frame.
2. Upload `DrawIrV3Command` + side tables as SSBOs **directly from columns**
   (they are already fixed-width SoA — this is the "direct assign" payoff);
   one dispatch consumes the command range instead of one dispatch per
   primitive. Push-constant packing per primitive disappears.
3. Command recording moves to the direct SFFI lane
   (`vkCmdBindPipeline/BindDescriptorSets/Dispatch` symbol table from S3).
4. Record perf receipts: primitives/frame vs dispatches/frame vs fence waits
   /frame, before/after. A regression here is a stop-ship for the stage.
- Exit: identical pixel hashes; dispatch count O(batches) not O(primitives);
  zero mid-frame descriptor/command-buffer allocation after warmup.

## S5 — Backend-aware one-time-allocation sizing

Files: `src/lib/common/ui/gpu_web_capacity_manifest.spl` (+ spec).

1. Add `GpuWebBackendStrideProfile` (per-record-kind stride + alignment for
   the selected backend) populated once at session creation beside the
   existing `..._for_backend_session` alignment probe.
2. Add `gpu_web_capacity_bytes(manifest, strides)` = counts × stride rounded
   to alignment; wire into verdict/breach (honesty rule unchanged: breach =
   rejection, no clamp, no auto-grow).
3. Embedded profile sizes by the **target** backend's strides at build time.
- Exit: `gpu_web_capacity_manifest_spec.spl` extended with per-backend stride
  cases; existing count-only callers unaffected (additive API).

## S6 — Metal/DX completion + wire cost note

1. Metal 2D switches fully to canonical columns + `*_mtl()` tables (done in
   S2); Metal 3D remains STUB — unblocking it is out of scope here, note it.
2. D3D12 stays aliased to the vkd3d shim; because the shim routes toward
   Vulkan dispatch, canonical-VK values pass through it **unremapped** — a
   free win; document it in the shim header.
3. File (do not fix here) the gpu-host wire cost: DrawIR crosses the daemon as
   SDN text and is re-parsed per frame; v3 has no serializer. A packed v3
   byte wire is the natural follow-up once S4 stabilizes the in-memory
   layout — record as a concrete follow-up plan entry, per the perf-regression
   rule.

## Order & rollback

S1→S2 are pure-value/rename stages (rollback = revert commit). S3 adds a
parallel lane (rollback = lane switch back to Rust externs). S4 is the only
stage that changes execution shape — it lands behind the existing
route/receipt mechanism (`draw_ir_v3_execution_route.spl`) so CPU_REFERENCE
remains selectable at any time. S5 is additive. Each stage is one push,
per-fix, immediately after its suite passes.
