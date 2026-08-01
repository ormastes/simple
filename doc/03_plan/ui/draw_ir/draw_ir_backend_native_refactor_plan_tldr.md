# DrawIR Backend-Native Layout Refactor — TLDR

Full plan: `draw_ir_backend_native_refactor_plan.md` · Arch:
`doc/04_architecture/ui/rendering/draw_ir_backend_native_layout.md`

**Finding:** DrawIR is NOT Vulkan-optimized today. No DrawIR struct ever
touches a Vk struct (all `Vk*CreateInfo` built in Rust; FFI = flat scalars);
rendering is per-primitive compute dispatch with a new descriptor set +
command buffer + fence-wait EACH primitive. Enum values already happen to be
raw VK numbers, but as unvalidated magic literals. Simple has no
setter-dispatch properties, so "assign wrapper" = accessor-function seam.
CUDA sees only scalars — excluded. Metal 2D real, DX = D3D11 subset,
D3D12 = vkd3d shim, WebGPU = stub.

**Decision:** v3 columns carry Vulkan-canonical values/layouts → Vulkan lane
is conversion-free (identity accessors, direct SFFI to libvulkan with packed
Vk records); Metal/DX remap on read via lookup tables (their numeric enums
genuinely differ: RGBA8 = VK 37 / MTL 70 / DXGI 28). v2 stays frozen oracle.

**Stages (each non-destructive, per-stage push):**
- S0 baseline receipts.
- S1 named VK-valued enums; widen `ResourceTable.formats` u16→u32 (VK ext
  formats overflow u16); replace magic numbers; range-validate before FFI.
- S2 accessor seam: `*_vk()` identity, `*_mtl()/*_dxgi()` tables.
- S3 packed Vk-record builders + direct `vkCreateImage(..., ptr)` SFFI lane
  (native only; interpreter keeps scalar externs; probe every symbol at
  session start — unregistered externs return nil silently).
- S4 perf: persistent descriptors, one cmdbuf+fence per frame, SSBO upload of
  v3 SoA columns as-is, dispatch per batch not per primitive.
- S5 capacity manifest gains per-backend stride profile → one-time allocation
  sized by counts × selected-backend stride (embedded: target backend).
- S6 Metal/DX table completion; file SDN-text wire cost as follow-up.
