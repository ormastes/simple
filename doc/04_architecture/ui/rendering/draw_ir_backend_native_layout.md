# DrawIR Backend-Native Internal Layout — Architecture

Status: DECIDED (2026-08-01). Companion plan:
`doc/03_plan/ui/draw_ir/draw_ir_backend_native_refactor_plan.md`.
Parent design: `doc/05_design/ui/rendering/draw_ir_multibackend_design.md` §12.

## 0. Decision

DrawIR keeps ONE public schema (v2 text oracle + v3 packed SoA), but the
**API-facing numeric domains and record layouts inside v3 are canonicalized to
Vulkan**: enum columns carry `VK_*` values verbatim and hot-path records are
laid out so the Vulkan backend consumes them with **zero conversion** (direct
column upload / pointer pass on the native lane). Metal and DirectX consume the
same records through a thin accessor seam that remaps values on read. CUDA is
out of scope for layout work: its kernels take decomposed scalars via
`void** kernelParams` and never see a descriptor struct
(`src/lib/gc_async_mut/gpu/engine2d/backend_cuda_launch_args.spl`).

**Direct-SFFI principle:** Simple reaches Vulkan through SFFI to the C
library (`libvulkan`) **directly wherever possible**. The Rust
`vulkan_graphics_runtime_*.rs` / `ash` layer is a compatibility lane
(interpreter mode, and calls that genuinely need host-side orchestration), not
the default. A packed Vk record built in Simple should land in
`vkCreateImage(device, &info, NULL, &image)` without being re-assembled by an
intermediary. See §3.5.

Rationale for Vulkan-first: the repo already passes raw VK numeric values
across the FFI today (`vulkan_backend3d.spl:73-78` hardcodes `37/43/9/126`;
usage flags as `0x43`, `0x23`, `0x12`, `0x35`; Rust does
`vk::Format::from_raw()` unvalidated). This architecture promotes that accident
to a checked contract instead of adding a conversion layer in front of it.

## 1. Current state (verified 2026-08-01)

### 1.1 How DrawIR actually reaches each API

| Backend | Reality | Path | Struct handling today |
|---|---|---|---|
| Vulkan 2D (DrawIR) | REAL | `draw_ir_adv.spl` executor → `backend_vulkan.spl` → `sffi_vulkan.spl` → Rust `ash` — SPIR-V **compute** dispatch (`vkCmdDispatch`), no `vkCmdDraw` | All `Vk*CreateInfo` built in Rust (`src/compiler_rust/runtime/src/vulkan/image.rs:117-135`); FFI is flat i64 scalars |
| Vulkan 3D | REAL | `GraphIr3D` → `vulkan_backend3d.spl` → `rt_vulkan_*_gfx` | Same: scalars in, Rust fills create-infos; DrawIR never enters this lane |
| Metal 2D/compute | REAL (macOS, objc2-metal) | `backend_metal.spl` → `metal_sffi.spl` → `metal_graphics_runtime.rs` | Scalars + i64 handles; no `MTLTextureDescriptor` on Simple side |
| Metal 3D | STUB (software fallback) | `gpu/engine3d/backend_metal.spl` | — |
| DirectX | REAL but **D3D11**, narrow (clear/fill/image/readback) | `sffi_directx.spl` packed u32 opcode stream → `runtime_directx_core.c` | No D3D types cross the boundary |
| D3D12 | SHIM (`vkd3d_d3d12.spl`, self-declared partial; selection aliases `d3d12→directx`) | routes toward Vulkan dispatch | — |
| WebGPU 3D | Interface real, backend STUB (interpreter externs return 0; no wgpu/dawn dep) | — | — |
| CUDA | REAL for compute; Linux gpu-host daemon **refuses CUDA for rendering** (`platform_all.spl:82-85`) | executor decomposes commands to i64 slot buffers | Never sees structs — excluded from layout goal |

### 1.2 Answer to "is DrawIR highly optimized for Vulkan?"

**No.** Three independent gaps, in priority order:

1. **Per-primitive submission**: `vulkan_sffi_dispatch_buffer_compute_checked`
   (`sffi_vulkan.spl:599-657`) creates a new descriptor set + command buffer +
   fence **per dispatch** and fence-waits — one CPU↔GPU sync per primitive.
   Descriptor sets are never cached in either lane.
2. **Per-primitive marshalling**: each primitive packs a fresh 48-byte
   push-constant array plus ~12 intermediate allocations (`_pack_i32_le`
   returns a new buffer per field, `backend_vulkan_helpers.spl:360-374`).
3. **No struct pass-through**: nothing on the Simple side is layout-compatible
   with any `Vk*` struct; every create-info is re-assembled field-by-field in
   Rust from scalar args.

The gpu-host wire adds a fourth cost: DrawIR crosses the daemon boundary as
canonical **SDN text** (`simpleos_host_gpu_draw_ir.spl:284`) and is re-parsed
into boxed structs per frame.

## 2. Full DrawIR inventory and per-item backend verdict

Verdict legend — **DIRECT**: assignable/uploadable as-is on Vulkan;
**REMAP**: same shape, values remapped per backend via accessor (O(1) table);
**WIDEN**: field size change required; **ASSEMBLE**: shape differs from the
API struct, needs one assembly step (candidate for packed-record pointer pass);
**HOST**: never crosses to a GPU API — no compatibility question.

### 2.1 v2 (`draw_ir.spl`) — CPU oracle, frozen

`DrawIrCommand` (text `kind`, text ids, nested `DrawIrRect`s, `[DrawIrStyleProp]`),
`DrawIrBatch`, `DrawIrComposition`, `DrawEdge`, `DrawIrGlyphRunPayload`,
`DrawIrEmbeddingConfig`, `DrawIrSourceInfo`, diff/patch types, SDN wire.
**Verdict: HOST, permanently.** Text-keyed boxed structs are not assignable to
any GPU API and v2's header freezes it as the CPU-reference oracle. No change.

### 2.2 v3 (`draw_ir_v3.spl`) — the layout target

| Item | Fields | Vulkan | Metal | DirectX | Notes |
|---|---|---|---|---|---|
| `DrawIrV3Command` | 2×u16 + 11×u32 (52 B fixed) | DIRECT (SSBO record, std430) | DIRECT | DIRECT* | *HLSL: pack the two u16 into one u32 or require SM6.2 16-bit types |
| `GeometryTable` | 5×[i32] | DIRECT | DIRECT | DIRECT | int columns, milli fixed-point consumed by shaders as int |
| `PaintTable.fill/stroke_colors` | [u32] RGBA | DIRECT | DIRECT | DIRECT | channel order vs swapchain format handled by shader swizzle, not data |
| `PaintTable.blend_modes` | [u16] opaque | **define = VK values** | REMAP | REMAP | today NO blend enum exists anywhere; 3D lane degrades blend to bool (`graphics.rs:305`). Encode as `VkBlendFactor` src/dst + `VkBlendOp` packed; Metal `MTLBlendFactor`/DX `D3D12_BLEND` differ numerically → table remap |
| `TextRunTable` | u32/i32/i64 columns | DIRECT | DIRECT | DIRECT | |
| `ResourceTable.formats` | [u16] opaque | **WIDEN → u32, values = `VkFormat`** | REMAP | REMAP | core VK formats fit u16 (0..184) but extension formats are `1000156xxx` — u16 CANNOT hold `VkFormat`; widen before assigning meaning |
| `ResourceTable.kinds/widths/heights/hashes` | u16/u32/i64 | DIRECT | DIRECT | DIRECT | |
| `PathPointTable.point_verbs` | [u16] MOVE/LINE/QUAD/CUBIC/CLOSE | HOST-domain | — | — | tessellated before any API; no VK counterpart, keep neutral |
| `ClipTable`, `TransformTable` | [i32] | DIRECT | DIRECT | DIRECT | consumed by compute kernels |
| `HitShapeTable`, `SourceProvenanceTable` | — | HOST | HOST | HOST | CPU hit-testing / tooling only |
| kind/flags/route/caps enums | u16/u32 | HOST | HOST | HOST | DrawIR-internal domains, no API counterpart |
| Image/texture creation (`ResourceTable` row → live texture) | — | **ASSEMBLE** | ASSEMBLE | ASSEMBLE | see §3 |
| Push-constant blocks | packed [u8], GLSL layout | DIRECT (`vkCmdPushConstants`) | DIRECT (`setBytes`) | DIRECT (root constants) | already byte-packed; keep |

### 2.3 Why image creation is ASSEMBLE, not DIRECT

`VkImageCreateInfo` is 88 bytes on x86_64 and contains `sType`, `pNext` (ptr),
and `pQueueFamilyIndices` (ptr). A pure-data column can never be
pointer-assigned to it without materializing those pointer fields. The
architecture therefore uses a **packed Vk-record lane**: Simple builds the
exact byte image of `VkImageCreateInfo` once (sType=14, pNext=0, ptrs=0,
SHARING_EXCLUSIVE) in a `[u8]` and the native FFI passes
`rt_array_data_ptr_u8` — precedent already exists for push constants
(`_vulkan_push_constants_abi`, `sffi_vulkan.spl:85-89`). Interpreter lane
keeps the scalar extern. Metal/DX shims read the same record through accessors
and fill `MTLTextureDescriptor` / `D3D11_TEXTURE2D_DESC` natively — they were
always assembling; nothing regresses.

## 3.5 Direct SFFI to libvulkan (bypass the Rust middle layer)

Target call shape on the native lane — no Rust re-assembly:

```
@extern fn vkCreateImage(device: i64, p_create_info: i64, p_allocator: i64,
                         p_image: i64) -> i32
# info = packed 88-byte VkImageCreateInfo built by Simple emit code
vkCreateImage(dev, rt_array_data_ptr_u8(info), 0, out_ptr)
```

- **Loader**: resolve symbols via `vkGetInstanceProcAddr`/`vkGetDeviceProcAddr`
  after instance/device creation (volk-style), or link `libvulkan.so.1`
  directly for core 1.x entry points. Instance/device bootstrap may stay on
  the existing Rust lane initially — it runs once; the win is the per-frame
  and per-resource calls.
- **Ownership boundary**: Simple owns create-info records and command-stream
  data; C/libvulkan owns handles. Handles remain opaque `i64` (unchanged).
- **Known traps** (must be engineered, not hoped): an unregistered
  `@extern fn` returns nil **silently** — every direct-VK symbol needs a
  registration probe + hard fail at session creation; new externs require a
  bootstrap rebuild; interpreter mode cannot take this lane and keeps the
  `rt_vulkan_*` scalar externs (dual-ABI switch as in
  `_vulkan_push_constants_abi`).
- **End state**: `rt_vulkan_*` Rust surface shrinks to (a) interpreter shims,
  (b) instance/device/queue bootstrap, (c) debug/validation plumbing. All
  steady-state resource creation, descriptor updates, command recording, and
  submission go Simple → SFFI → libvulkan.

### 2.4 Enum value cross-table (why "values actually same" holds only for Vulkan)

| Meaning | VkFormat (canonical) | MTLPixelFormat | DXGI_FORMAT |
|---|---|---|---|
| RGBA8 Unorm | 37 | 70 | 28 |
| RGBA8 sRGB | 43 | 71 | 29 |
| BGRA8 Unorm | 44 | 80 | 87 |
| R8 Unorm | 9 | 10 | 61 |
| Depth32 Float | 126 | 252 | 40 |

The three APIs disagree numerically on every row → cross-backend value
identity is impossible; canonical-Vulkan + read-side remap tables is the
cheapest correct scheme, and makes the Vulkan path conversion-free.

## 3. The accessor seam (in place of property wrappers)

The Simple language has **no computed properties**: reads can look like field
access (no-paren method call `obj.x` ≡ `obj.x()`), but `obj.x = v` is always a
raw store — there is no setter dispatch anywhere in the compiler. The "same
DrawIR, backend-native internal struct" goal is therefore implemented as an
**accessor-function seam**, not a transparent wrapper:

- Columns store canonical (VK) values. Producers write via emit kernels only
  (already true in v3 — accessor views are read-only snapshots with
  `present:bool`).
- Backend read accessors: `paint_blend_vk(p)` is **identity** (satisfies
  "Vulkan needs no wrapper in most cases"), `paint_blend_mtl(p)` /
  `resource_format_dxgi(r)` are static lookup-table remaps.
- FFI shims validate range before `from_raw` — closes the existing
  unvalidated `vk::Format::from_raw` hole.

If transparent setter dispatch is ever wanted, that is a language feature
request (file separately); this architecture does not depend on it.

## 4. One-time allocation sizing must be backend-aware — design update REQUIRED

`gpu_web_capacity_manifest.spl` already does count → scan → verify → emit with
no mid-frame realloc, and `..._for_backend_session()` injects backend
**alignment** and preprocess bytes. What it lacks: capacity is element counts
with strides implied by fixed-width records — there is **no counts×stride byte
computation**, so a backend-dependent record size is invisible to the verdict.

Required additions (additive, no behavior change until used):

1. `GpuWebBackendStrideProfile` — per-record-kind byte stride + alignment for
   the *selected* backend, queried once at session creation next to the
   existing alignment probe: command record (52 B canonical; DX u16-packing
   may pad to 56), per-table column strides, packed create-record sizes
   (Vk image record 88 B; Metal/DX equivalents live native-side → 0).
2. `gpu_web_capacity_bytes(manifest, strides)` — counts × stride, rounded to
   backend alignment, summed per pool; feeds the existing verdict/breach path
   (honesty rule unchanged: breach = rejection receipt, no clamp, no grow).
3. Embedded profile ("allocate exact maximum once") multiplies by the
   **target** backend's strides at build time, not the host's.

## 5. Invariants

- v2 is never modified (frozen oracle; its SDN wire and diff/patch stay).
- v3 changes are additive except the single `formats` u16→u32 widening (v3 has
  no serializer — in-memory only, callers enumerated in the plan).
- Every stage keeps interpreter and native lanes green; interpreter keeps
  scalar externs (packed-record lane is native-only, selected by the existing
  dual-ABI pattern).
- No silent fallback: a backend that cannot honor a canonical value must
  reject with a receipt (`DrawIrV3SubmitReceipt`), per the honesty model.
