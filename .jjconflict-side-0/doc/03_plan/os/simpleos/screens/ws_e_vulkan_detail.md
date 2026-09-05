# Workstream E — Vulkan on SimpleOS via Venus over virtio-gpu (detail plan)

Parent: `doc/03_plan/os/simpleos/screens_showcase_2d_opt_plan.md` §Workstream E.
Design: `doc/05_design/os/desktop/screen_backend_selection_and_shared_showcase.md` §2.6.
Lane state: `.spipe/simpleos-screens-render-lane/state.md` AC-9.
Feeds (does **not** duplicate): `doc/03_plan/os/simpleos_multiconfig_vulkan_wm_plan.md` +
`..._tldr.md`, `.spipe/simpleos-multiconfig-vulkan-wm/state.md`.

**Scope statement (read first):** QEMU-only. virtio-gpu is a paravirtual device;
Venus is a host-renderer protocol. No physical-GPU/board claim is made or implied
by any task here. See §7 for the filed board blocker text.

---

## 0. Ground truth in the repo today

### 0.1 virtio-gpu driver — 2D only (1,710 lines across 5 files)

| File | Lines | What it does |
|---|---|---|
| `src/os/drivers/virtio/virtio_gpu.spl` | 810 | `VirtioGpuDriver` class, BAR/MMIO accessors, controlq setup (`VIRTIO_GPU_CONTROLQ` at :67, :295, :413), `notify_queue(VIRTIO_GPU_CONTROLQ)` at :629 |
| `virtio_gpu_init.spl` | 303 | modern + legacy init/feature negotiation |
| `virtio_gpu_ops.spl` | 380 | 2D command builders/submitters |
| `virtio_gpu_regs.spl` | 128 | virtqueue geometry (`virtqueue_desc_size` :76 … `virtqueue_total_size` :85), raw RAM/MMIO helpers, externs :13-20 |
| `virtio_gpu_types.spl` | 89 | opcodes, formats, struct sizes |

Commands implemented — **all 2D, nothing else** (`virtio_gpu_types.spl:13-20`,
re-exported `virtio_gpu.spl:26-31`):

```
0x0100 GET_DISPLAY_INFO      0x0101 RESOURCE_CREATE_2D
0x0102 RESOURCE_UNREF        0x0103 SET_SCANOUT
0x0104 RESOURCE_FLUSH        0x0105 TRANSFER_TO_HOST_2D
0x0106 RESOURCE_ATTACH_BACKING  0x0107 RESOURCE_DETACH_BACKING
0x0300 UPDATE_CURSOR         0x0301 MOVE_CURSOR
```
Responses handled: `0x1100 RESP_OK_NODATA`, `0x1101 RESP_OK_DISPLAY_INFO`, plus
error codes `0x1200..0x1203`.

**Absent entirely** (must be added by E1/E2): `GET_CAPSET_INFO (0x0108)`,
`GET_CAPSET (0x0109)`, `GET_EDID (0x010a)`, `RESOURCE_ASSIGN_UUID (0x010b)`,
`RESOURCE_CREATE_BLOB (0x010c)`, `SET_SCANOUT_BLOB (0x010d)`,
`CTX_CREATE (0x0200)`, `CTX_DESTROY (0x0201)`,
`CTX_ATTACH_RESOURCE (0x0202)`, `CTX_DETACH_RESOURCE (0x0203)`,
`RESOURCE_CREATE_3D (0x0204)`, `TRANSFER_TO_HOST_3D (0x0205)`,
`TRANSFER_FROM_HOST_3D (0x0206)`, `SUBMIT_3D (0x0207)`,
`RESOURCE_MAP_BLOB (0x0208)`, `RESOURCE_UNMAP_BLOB (0x0209)`;
responses `0x1102 RESP_OK_CAPSET_INFO`, `0x1103 RESP_OK_CAPSET`,
`0x1105 RESP_OK_RESOURCE_UUID`, `0x1106 RESP_OK_MAP_INFO`. There is also **no
cursorq** wired and **no second queue** — only `VIRTIO_GPU_CONTROLQ`.

### 0.2 Feature negotiation today writes ZERO device features

`virtio_gpu_init.spl`:
- modern path :48-57 — reads `host_features` (logged, :50), then writes
  `DRIVER_FEATURE[select=0] = 0` (:51-52) and `DRIVER_FEATURE[select=1] = 1`
  (:53-54, i.e. only `VIRTIO_F_VERSION_1`, bit 32). **No device feature bit is
  ever acked.**
- legacy paths :142-144 and :241-243 — `write_reg32(VIRTIO_PCI_GUEST_FEATURES, 0)`.

So `VIRTIO_GPU_F_VIRGL (bit 0)`, `EDID (1)`, `RESOURCE_UUID (2)`, `RESOURCE_BLOB
(3)`, `CONTEXT_INIT (4)` are all currently rejected by construction. E1 is
precisely about this.

### 0.3 Kernel syscalls that already exist (build on these, do not re-add)

`src/os/kernel/abi/syscall_shim_device.spl`:
- **83 `map_bar`** — `spl_handle_map_bar` :85-95, marked `[IMPLEMENTED]`,
  a0=device id, a1=BAR index, a2=out user-VA ptr; forwards to `_handle_map_bar()`
  in `syscall.spl`.
- **84 `alloc_dma`** — `spl_handle_alloc_dma` :104-..., `[IMPLEMENTED]`,
  a0=size, a1=alignment (pow2, min 4096), a2=out **physical** address ptr;
  returns VA. This is exactly the primitive Venus shmem rings need.
- 82 `device_grant` :70-76 (grant/claim a device to the caller).

PCI enumeration: `src/os/drivers/pci/pci.spl`, `pci_provider.spl`,
`pci_bar64.spl` (64-bit BAR decode — needed for the blob/shmem BAR).

### 0.4 `vulkan_icd_virtio.spl` — 182 lines, fully modeled

Header self-documents: *"the transport layer uses modeled responses pending
virtio-gpu kernel driver integration."* Exact modeled surface to be deleted in E3:

| Symbol | Line | Modeled behavior |
|---|---|---|
| `_venus_transport_send` | :52 | increments `_venus_handle_ctr`, returns `is_ok: true` with a fake handle. **Never touches a ring.** |
| `venus_icd_connect` | :65 | sets `_venus_connected=true` from a string path, no device open |
| `venus_icd_disconnect` | :83 | clears globals |
| `venus_icd_is_connected` | :90 | returns the global bool |
| `venus_icd_create_instance` | :98 | `_venus_transport_send(op 1)` |
| `venus_icd_create_device` | :109 | `_venus_transport_send(op 2)` |
| `venus_icd_allocate_memory` | :126 | `_venus_transport_send(op 3)` |
| `venus_icd_create_buffer` | :144 | `_venus_transport_send(op 4)` |
| `venus_icd_destroy_instance` | :161 | `_venus_transport_send(op 5)` |
| `venus_icd_protocol_version` | :174 | returns stored int |

Local opcode enum `VENUS_OP_CREATE_INSTANCE..DESTROY_INSTANCE = 1..5`
(:39-43) is **invented, not Venus**. Real Venus command ids come from the
`venus_protocol` encoding (`VkCommandTypeEXT`), not from 1..5.

Siblings in the same directory (context for where the ICD plugs in):
`vulkan_loader.spl`, `vulkan_dispatch.spl`, `vulkan_icd_sffi.spl` (host ICD via
SFFI), `sffi_vulkan.spl`, and `engine2d/backend.spl` + `engine2d/backend_lane.spl`
(where a `DrawIrV3` / Engine2D command stream would select a backend).

### 0.5 Host-only real Vulkan (oracle ONLY — never a SimpleOS claim)

`src/compiler_rust/runtime/src/vulkan*` and `src/compiler/70.backend/backend/vulkan*`
run on the **host** loader/ICD. They may be used to produce a reference clear-image
checksum for E3, and for nothing else. Any evidence row derived from them must
carry `source=host-oracle`.

### 0.6 The published QEMU args cannot do Venus

`scripts/check/check_simpleos_multiconfig_live_evidence.spl:145` requires
`simpleos_engine2d_qemu_gpu_device == "virtio-gpu-pci,disable-modern=on,disable-legacy=off"`.
That is the **legacy 2D transport** — `disable-modern=on` forces the legacy PCI
register window, and plain `virtio-gpu-pci` has no host renderer at all. It will
never expose `VIRTIO_GPU_F_VIRGL` or a Venus capset. E4 must widen that check
(§4.2), not silently satisfy it.

---

## E1 — 3D/context-init feature negotiation + capset discovery  *(model: opus)*

**Objective:** the existing driver negotiates `VIRTIO_GPU_F_VIRGL` and
`VIRTIO_GPU_F_CONTEXT_INIT` (and `RESOURCE_BLOB`), then discovers the **Venus**
capset id + max version from a live QEMU boot and logs them.

### E1.1 Add the missing constants
File: `src/os/drivers/virtio/virtio_gpu_types.spl` (append next to :13-51).

```simple
# Device feature bits (virtio-gpu)
val VIRTIO_GPU_F_VIRGL: u64 = 1 << 0
val VIRTIO_GPU_F_EDID: u64 = 1 << 1
val VIRTIO_GPU_F_RESOURCE_UUID: u64 = 1 << 2
val VIRTIO_GPU_F_RESOURCE_BLOB: u64 = 1 << 3
val VIRTIO_GPU_F_CONTEXT_INIT: u64 = 1 << 4

val VIRTIO_GPU_CMD_GET_CAPSET_INFO: u32 = 0x0108
val VIRTIO_GPU_CMD_GET_CAPSET: u32     = 0x0109
val VIRTIO_GPU_RESP_OK_CAPSET_INFO: u32 = 0x1102
val VIRTIO_GPU_RESP_OK_CAPSET: u32      = 0x1103

# capset ids (virtio_gpu.h)
val VIRTIO_GPU_CAPSET_VIRGL: u32   = 1
val VIRTIO_GPU_CAPSET_VIRGL2: u32  = 2
val VIRTIO_GPU_CAPSET_VENUS: u32   = 4

val GET_CAPSET_INFO_SIZE: u64 = 32     # hdr(24) + capset_index(4) + pad(4)
val RESP_CAPSET_INFO_SIZE: u64 = 40    # hdr(24) + id,max_version,max_size(12) + pad(4)
val GET_CAPSET_SIZE: u64 = 32          # hdr(24) + capset_id(4) + capset_version(4)
```

### E1.2 Negotiate, don't zero
File: `virtio_gpu_init.spl`, modern path :48-57 (and mirror the decision in the
legacy paths :142-144 / :241-243 by *refusing* 3D there — legacy cannot do Venus).

```simple
val want_lo = VIRTIO_GPU_F_VIRGL | VIRTIO_GPU_F_RESOURCE_BLOB | VIRTIO_GPU_F_CONTEXT_INIT
val acked_lo = host_features & want_lo          # only ack what the host offers
drv.modern_write32(MODERN_COMMON_DRIVER_FEATURE_SELECT, 0)
drv.modern_write32(MODERN_COMMON_DRIVER_FEATURE, acked_lo)
drv.modern_write32(MODERN_COMMON_DRIVER_FEATURE_SELECT, 1)
drv.modern_write32(MODERN_COMMON_DRIVER_FEATURE, 1)   # VIRTIO_F_VERSION_1, unchanged
log_info("[virtio-gpu] acked_features=0x{acked_lo} virgl={..} blob={..} ctxinit={..}")
drv.has_3d = (acked_lo & VIRTIO_GPU_F_VIRGL) != 0
drv.has_blob = (acked_lo & VIRTIO_GPU_F_RESOURCE_BLOB) != 0
drv.has_ctx_init = (acked_lo & VIRTIO_GPU_F_CONTEXT_INIT) != 0
```
Add the three `bool` fields to `VirtioGpuDriver` in `virtio_gpu.spl`. Existing 2D
behavior must be byte-identical when the host offers nothing (`acked_lo == 0`) —
that is the regression guard.

Also read `num_capsets` from the device config space (`virtio_gpu_config`
offset 8) once features are OK; today the driver never reads it.

### E1.3 Capset walk
New file: `src/os/drivers/virtio/virtio_gpu_capset.spl`.

```simple
class GpuCapset:
    id: u32
    max_version: u32
    max_size: u32

fn gpu_query_capsets(drv: VirtioGpuDriver) -> List<GpuCapset>:
    # for i in 0..num_capsets: GET_CAPSET_INFO(capset_index=i)
    #   -> RESP_OK_CAPSET_INFO { capset_id, capset_max_version, capset_max_size }
fn gpu_find_venus(caps: List<GpuCapset>) -> GpuCapset?   # id == VIRTIO_GPU_CAPSET_VENUS
fn gpu_get_capset(drv, id: u32, version: u32) -> List<u8>  # GET_CAPSET blob
```
Submission reuses the existing controlq descriptor path in `virtio_gpu_ops.spl`
(one device-readable request desc + one device-writable response desc). Do not
open a new queue for E1.

### E1.4 Corrected QEMU invocation

**These are the args E1 is verified against.** The 2D args in §0.6 are kept only
for the existing 2D lanes.

x86_64 host, riscv64 guest (matching the multiconfig lane profile):
```
qemu-system-riscv64 -M virt -m 2G -smp 2 \
  -device virtio-gpu-gl-pci,hostmem=256M,blob=true,venus=true,context_init=true \
  -display sdl,gl=on \
  ... (existing OpenSBI/EDK2 firmware + disk args unchanged) \
  -qmp unix:$QMP,server,nowait -serial file:$SERIAL
```
Headless capture variant (for CI): `-display egl-headless,gl=on` plus the existing
QMP `screendump`. `-display none` **disables the GL renderer** and must not be used
for E-lane runs.

Host prerequisites, all of which must be asserted before a run is called live:
- QEMU built with `--enable-virglrenderer --enable-opengl` and virglrenderer
  ≥ 0.10 built `-Dvenus=true` (`qemu-system-riscv64 -device help | grep virtio-gpu-gl`
  must list the device; `venus=true` must be an accepted property).
- A **host Vulkan 1.2+ driver** (`vulkaninfo --summary` succeeds on the host).
  Venus is a passthrough protocol: no host Vulkan → no guest Vulkan.
- `VIRGL_VENUS=1` (or the distro equivalent) in the QEMU environment where the
  virglrenderer build requires the opt-in.
- x86_64/aarch64 guest variant: `-device virtio-vga-gl,blob=true,venus=true`.

### E1.5 Acceptance
```
sh scripts/check/check-simpleos-venus-capset.shs        # NEW wrapper, E1 deliverable
```
Expected on stdout, extracted from the **live serial log** of the boot above:
```
[virtio-gpu] host_features=0x<nonzero>
[virtio-gpu] acked_features=0x1d virgl=1 blob=1 ctxinit=1
[virtio-gpu] num_capsets=2
[virtio-gpu] capset[0] id=2 max_version=<n> max_size=<n>   # VIRGL2
[virtio-gpu] capset[1] id=4 max_version=<n> max_size=<n>   # VENUS
simpleos_venus_capset_status=pass
simpleos_venus_capset_id=4
simpleos_venus_capset_max_version=<n>
```
Fail-closed: absent serial line ⇒ `blocked:no-live-serial`; `capset id=4` absent
⇒ `blocked:venus-capset-not-exposed` (→ §6 STOP check). The status must be
derived from grepping the captured serial file, never printed by the wrapper on
its own authority.

**Deps:** none. **Model:** opus.

---

## E2 — 3D context, blob resources, ring transport, fencing  *(model: opus)*

**Objective:** a Venus-capable context exists, a shared-memory command ring is
allocated from guest DMA memory and attached to the context, and a byte buffer
can be round-tripped through `SUBMIT_3D` with a completion fence.

### E2.1 Module layout (new files, all under the existing driver dir)
```
src/os/drivers/virtio/virtio_gpu_3d.spl      # CTX_CREATE/DESTROY, SUBMIT_3D, ctx resource attach
src/os/drivers/virtio/virtio_gpu_blob.spl    # RESOURCE_CREATE_BLOB / MAP_BLOB / UNMAP_BLOB
src/os/drivers/virtio/virtio_gpu_fence.spl   # fence_id allocation + wait
src/os/drivers/virtio/venus_ring.spl         # Venus shmem ring header + producer/consumer
```
`virtio_gpu_types.spl` gains the 0x0200-0x0209 opcodes and 0x1106 `RESP_OK_MAP_INFO`.

### E2.2 Context create
```simple
val VIRTIO_GPU_CMD_CTX_CREATE: u32 = 0x0200
val VIRTIO_GPU_CONTEXT_INIT_CAPSET_ID_MASK: u32 = 0x000000ff

# ctx_create payload: hdr(24) + nlen u32 + context_init u32 + debug_name[64] = 96 bytes
struct GpuCtxCreate:
    hdr: GpuCtrlHdr        # type=0x0200, ctx_id = <allocated>
    nlen: u32
    context_init: u32      # = VIRTIO_GPU_CAPSET_VENUS  (capset id in low 8 bits)
    debug_name: [u8; 64]   # "simpleos-venus"
```
`hdr.ctx_id` is a driver-allocated small integer (1-based); every subsequent 3D
command carries it. `context_init` is only legal when `has_ctx_init` from E1.2 —
otherwise refuse and return an explicit error, never fall back to a 2D context.

### E2.3 Blob resources for the ring (uses syscalls 83/84)
```simple
val VIRTIO_GPU_CMD_RESOURCE_CREATE_BLOB: u32 = 0x010c
val VIRTIO_GPU_BLOB_MEM_GUEST: u32       = 1
val VIRTIO_GPU_BLOB_MEM_HOST3D: u32      = 2
val VIRTIO_GPU_BLOB_FLAG_USE_MAPPABLE: u32 = 1
val VIRTIO_GPU_BLOB_FLAG_USE_SHAREABLE: u32 = 2

# create_blob payload: hdr(24) + resource_id,blob_mem,blob_flags,nr_entries (16)
#                      + blob_id u64 (8) + size u64 (8) + mem_entries[nr_entries]
```
Allocation path — **do not invent a new allocator**:
1. `syscall 84 alloc_dma(size = ring_bytes, align = 4096, out_phys)` →
   returns user VA, writes the physical address. One entry per 4 KiB page becomes
   a `virtio_gpu_mem_entry { addr u64, length u32, pad u32 }`.
2. `RESOURCE_CREATE_BLOB` with `blob_mem = VIRTIO_GPU_BLOB_MEM_GUEST`,
   `blob_flags = USE_MAPPABLE|USE_SHAREABLE`, `nr_entries = pages`.
3. `CTX_ATTACH_RESOURCE (0x0202)` binds it to the Venus context.
4. Host-visible blobs (`BLOB_MEM_HOST3D`) additionally need
   `RESOURCE_MAP_BLOB (0x0208)` → `RESP_OK_MAP_INFO` giving an offset into the
   device's **shared-memory region (shmid 0)**, which is reached via
   `syscall 83 map_bar(dev, bar_index, out_va)` on the 64-bit shmem BAR decoded by
   `src/os/drivers/pci/pci_bar64.spl`. E2 minimum viable uses `BLOB_MEM_GUEST`
   only; `HOST3D` mapping is E2 stretch and may be deferred to E3.

### E2.4 Venus ring
`venus_ring.spl` — the ring layout is defined by the Venus capset blob fetched in
E1.3 (`vn_info_extension_spec_version` / renderer capset v0 header); parse it,
never hardcode:
```simple
class VenusRing:
    shmem_va: u64        # from alloc_dma
    shmem_phys: u64
    size: u64            # power of two, from capset max_size, default 1<<20
    head_off: u64        # producer cursor, guest-written
    tail_off: u64        # consumer cursor, host-written
    buffer_off: u64
    extra_off: u64       # status/reply area

fn ring_init(cfg: VenusRingCfg) -> VenusRing
fn ring_write_cmd(r: VenusRing, bytes: List<u8>) -> bool   # wraps, respects tail
fn ring_read_reply(r: VenusRing, out: MutList<u8>, fence: u64) -> bool
```
Memory-order requirement: the guest must publish the payload **before** the head
update, and must re-read `tail` with an acquire fence. Use the existing raw
accessors in `virtio_gpu_regs.spl:94-127` (`ram_write32/64`, `ram_read32/64`) plus
an explicit `fence` intrinsic; do **not** rely on `rt_mem_*_boxed` for ring
cursors (boxed reads go through a different path — see traps §8).

### E2.5 Submit + fence
```simple
val VIRTIO_GPU_CMD_SUBMIT_3D: u32 = 0x0207
val VIRTIO_GPU_FLAG_FENCE: u32 = 1 << 0
# submit_3d payload: hdr(24) + size u32 + padding u32 + <cmd stream bytes>
```
`hdr.flags |= VIRTIO_GPU_FLAG_FENCE`, `hdr.fence_id = <monotonic u64>`,
`hdr.ring_idx` = Venus ring index when `CONTEXT_INIT` is negotiated.
Completion = the controlq used-ring entry for that descriptor **plus** the host
having advanced the ring `tail` past our head. Poll both; timeout is a hard
failure, not a retry-forever.

### E2.6 Acceptance
```
sh scripts/check/check-simpleos-venus-ring.shs           # NEW wrapper, E2 deliverable
```
Expected in the live serial capture:
```
[virtio-gpu] ctx_create ctx_id=1 capset=4 resp=0x1100
[virtio-gpu] blob res_id=8 size=1048576 pages=256 resp=0x1100
[virtio-gpu] ctx_attach res_id=8 resp=0x1100
[venus] ring init size=1048576 head=0 tail=0
[venus] submit_3d bytes=<n> fence_id=1 -> used_ring ok, tail advanced to <n>
simpleos_venus_ring_status=pass
```
A pass requires `tail` to have **moved** — a `RESP_OK_NODATA` alone proves only
that the device parsed the header, not that the host renderer consumed the
stream. Encode that in the wrapper.

**Deps:** E1. **Model:** opus.

---

## E3 — real transport behind `vulkan_icd_virtio.spl`  *(model: opus)*

**Objective:** every modeled response in §0.4 is replaced by an encode → ring →
`SUBMIT_3D` → fence → decode round trip, and a Vulkan clear is proven by a
checksum read back from **device** memory.

### E3.1 Deletions (exhaustive; nothing in this list may survive)
In `src/lib/nogc_async_mut/gpu/vulkan_icd_virtio.spl`:
- `_venus_transport_send` (:52) — delete the body entirely; the `_venus_handle_ctr`
  fabrication is the single worst artifact in the file.
- `_venus_handle_ctr` global (:37) — delete. Handles come from decoded replies.
- `VENUS_OP_CREATE_INSTANCE..VENUS_OP_DESTROY_INSTANCE` (:39-43) — delete; replace
  with generated `VkCommandTypeEXT` ids from the Venus protocol tables.
- `venus_icd_connect` (:65) — replace `device_path: text` + bool flip with a real
  open: PCI probe → `map_bar` → E1 capset check → E2 `ctx_create` + `ring_init`.
  Failure returns `false` with a reason string; it may not return `true` without
  a live context.
- `venus_icd_create_instance` (:98) / `create_device` (:109) /
  `allocate_memory` (:126) / `create_buffer` (:144) / `destroy_instance` (:161) —
  each becomes encode+submit+decode. A reply that does not arrive is an error,
  not a synthesized handle.
- `venus_icd_protocol_version` (:174) — must return the version reported by the
  E1 capset (`capset_max_version`), not `_venus_protocol_version` set by the caller.
- Header docstring (:1-9) — rewrite; the "modeled responses" disclaimer must go
  away only in the same commit that removes the modeling.

New sibling: `src/lib/nogc_async_mut/gpu/venus_encoder.spl` (command serialization
+ reply decoding), kept separate from the ICD entry points so the encoder is
unit-testable against captured byte streams.

### E3.2 Minimum viable proof (the whole point of E3)
A guest-side program that does, over the real transport, in order:
1. `vkCreateInstance`
2. `vkEnumeratePhysicalDevices` → **≥1**, and
   `vkGetPhysicalDeviceProperties.deviceName` printed verbatim
3. `vkCreateDevice` + one graphics/compute queue
4. `vkCreateImage` (or buffer) in `DEVICE_LOCAL` memory, `vkCmdClearColorImage`
   to a known non-uniform color, submit, `vkQueueWaitIdle`
5. `vkCmdCopyImageToBuffer` into `HOST_VISIBLE` memory, map, **checksum the bytes**
6. Compare against the host-oracle checksum from §0.5 for the same clear color
   and extent.

New file: `src/os/apps/venus_smoke.spl` (guest binary) +
`scripts/check/check-simpleos-venus-clear-readback.shs` (host wrapper).

### E3.3 Honesty rule (non-negotiable)
- Software/llvmpipe/lavapipe execution, host-side emulation, CPU rasterization,
  or any Engine2D CPU/SIMD fallback **may not satisfy a Vulkan claim.** If
  `deviceName` matches `llvmpipe|lavapipe|SwiftShader|Software`, the run emits
  `simpleos_venus_device_class=software` and the Vulkan status is
  `blocked:software-renderer`, never `pass`.
- Any value not read from a live guest run is emitted with a `modeled:` prefix and
  is fail-closed at every gate.
- Deleting the modeled functions and leaving the callers to fall back to
  `vulkan_icd_sffi.spl` (host ICD) is a **cover-up**, not a fix: the ICD selection
  must record which ICD served the call (`simpleos_venus_icd=virtio|sffi`) and
  `sffi` never counts for a SimpleOS claim.

### E3.4 Acceptance
```
sh scripts/check/check-simpleos-venus-clear-readback.shs
```
Expected:
```
[venus] instance ok
[venus] physical_devices=1 name="Virtio-GPU Venus (<host GPU name>)"
[venus] device+queue ok qfam=0
[venus] clear rgba=(0x33,0x77,0xCC,0xFF) extent=256x256 submitted fence=7
[venus] readback bytes=262144 checksum=<hex>
simpleos_venus_icd=virtio
simpleos_venus_device_class=hardware
simpleos_venus_clear_checksum=<hex>
simpleos_venus_clear_status=pass
```
plus `checksum == host-oracle checksum`. Mismatch ⇒
`blocked:checksum-mismatch-vs-oracle` (a real failure worth investigating, not a
tolerance to widen).

**Deps:** E2. **Model:** opus.

---

## E4 — evidence plumbing into the multiconfig gates  *(model: sonnet)*

**Objective:** E1-E3 output feeds the **existing** multiconfig evidence keys. No
new parallel gate campaign.

### E4.1 Keys fed (existing, from `check_simpleos_multiconfig_live_evidence.spl`)

| Existing key | Fed by | Value from |
|---|---|---|
| `simpleos_engine2d_runtime_backend` (:118, must be `vulkan`) | E3 | ICD selection, only when `simpleos_venus_icd=virtio` |
| `simpleos_engine2d_vulkan_device_name` (:124, must be non-empty) | E3.2 step 2 | live `deviceName` |
| `simpleos_engine2d_viewport_width` / `_height` (:126-129, positive) | E3.2 step 4 | image extent |
| `simpleos_engine2d_readback_checksum` (:130) | E3.2 step 5 | device-memory readback |
| `simpleos_engine2d_readback_nonblank_status` (:132, must be `pass`) | E3.2 | nonblank check on the readback |
| `simpleos_engine2d_device_readback_required` (:151, must be `true`) | E3 | set true for this lane |
| `simpleos_engine2d_scene` (:120/:147, `vulkan-engine2d`) | E3+Engine2D bridge | scene name |
| `simpleos_engine2d_drawing_backend` (:141, `virtio_gpu`) | E1/E2 | unchanged |
| `simpleos_engine2d_processing_backend` (:143, `vulkan`) | E3 | ICD |
| `simpleos_engine2d_vulkan_bridge_status` (:138, printed :292) | derived | all of the above |
| `simpleos_engine2d_vulkan_evidence_status` (:258, :355) | derived | all of the above |
| `simpleos_renderdoc_rdc_magic_status` / `..._rdc_magic=RDOC` | E4.3 | captured `.rdc` |

New keys this workstream adds (all fail-closed, default `blocked:not-run`):
`simpleos_venus_capset_status`, `simpleos_venus_capset_id`,
`simpleos_venus_capset_max_version`, `simpleos_venus_ring_status`,
`simpleos_venus_icd`, `simpleos_venus_device_class`,
`simpleos_venus_clear_checksum`, `simpleos_venus_clear_status`,
`simpleos_venus_board_runnable_status` (always
`blocked:qemu-only-virtio-gpu`, see §7).

### E4.2 Required edit to the QEMU-device assertion
`scripts/check/check_simpleos_multiconfig_live_evidence.spl:145` currently
hard-equals the **2D legacy** device string (§0.6). Change it to an allow-list
keyed by lane, so the 2D lane keeps its exact string and the Venus lane requires
a GL device:
```simple
val dev = evidence_text_or(raw, "simpleos_engine2d_qemu_gpu_device", "")
val is_2d_lane = dev == "virtio-gpu-pci,disable-modern=on,disable-legacy=off"
val is_venus_lane = dev.starts_with("virtio-gpu-gl-pci") or dev.starts_with("virtio-vga-gl")
if evidence_text_or(raw, "simpleos_engine2d_processing_backend", "") == "vulkan":
    if not is_venus_lane: return "blocked:vulkan-lane-on-2d-qemu-device"
    if not dev.contains("venus=true"): return "blocked:venus-not-enabled-on-qemu-device"
else:
    if not is_2d_lane: return "blocked:unexpected-qemu-gpu-device"
```
This is a **tightening**, not a loosening: it makes the existing lane's implicit
assumption explicit and blocks a Vulkan claim made on the 2D device.

### E4.3 Wrappers
- `scripts/check/check-simpleos-engine2d-renderdoc-evidence.ps1` — extend to
  ingest the E3 run's `.rdc` (validated by `RDOC` magic; raw magic alone is
  insufficient per the design doc §"Validate .rdc files by RDOC magic").
- `scripts/check/check_simpleos_multiconfig_live_evidence.spl` — E4.1 rows + E4.2 edit.
- `scripts/check/check-simpleos-multiconfig-live-evidence.ps1` — surface the new rows.
- New: `check-simpleos-venus-capset.shs` (E1), `check-simpleos-venus-ring.shs` (E2),
  `check-simpleos-venus-clear-readback.shs` (E3).

### E4.4 Fail-closed default
Every new key defaults to `blocked:not-run`. A key is `pass` **only** when parsed
out of a captured artifact (serial log file, QMP screendump, `.rdc`) produced by
that run. No wrapper prints `pass` from its own control flow. Missing artifact ⇒
`blocked:no-artifact`, never absent-row-treated-as-pass.

### E4.5 Acceptance
```
bin/simple run scripts/check/check_simpleos_multiconfig_live_evidence.spl
```
Before E1-E3 land, expected (proving fail-closed is real):
```
simpleos_venus_capset_status=blocked:not-run
simpleos_venus_ring_status=blocked:not-run
simpleos_venus_clear_status=blocked:not-run
simpleos_engine2d_vulkan_bridge_status=blocked:<existing reason>
simpleos_venus_board_runnable_status=blocked:qemu-only-virtio-gpu
```
After: the first three flip to `pass` and
`simpleos_engine2d_vulkan_bridge_status=pass`; the board row **stays blocked**.

**Deps:** E1-E3 for the values; E4.2 + E4.4 can land first as fail-closed
scaffolding. **Model:** sonnet.

---

## 5. Minimum viable landing vs. full Engine2D-on-Vulkan

**MVL (what E1-E4 commit to):** capsets discovered live; one Venus context; one
guest-memory ring; one `SUBMIT_3D` round trip with a fence; instance → physical
device → device+queue → clear an image → checksum from device memory matching the
host oracle; evidence rows flipped from a captured artifact. **No Engine2D
content, no WM, no swapchain, no presentation.** The cleared image never reaches a
scanout.

**Full (explicitly out of scope here):** `VK_KHR_swapchain` over
`SET_SCANOUT_BLOB`, Engine2D `DrawIrV3` command translation in
`src/lib/nogc_async_mut/gpu/engine2d/backend.spl` + `backend_lane.spl`, pipeline
cache, per-frame fencing, the WM compositor on Vulkan, multi-queue.
Each is a separate follow-on plan and none may be claimed by E1-E4 evidence.

---

## 6. STOP / park criterion

Park the workstream — do not push through — when any of:
1. E1.5 reports `blocked:venus-capset-not-exposed` after the host prerequisites in
   E1.4 are individually verified (QEMU lists `virtio-gpu-gl`, virglrenderer built
   with venus, host `vulkaninfo` succeeds).
2. The host has no working Vulkan driver, or only a software one — Venus cannot
   manufacture a GPU.
3. E3 can only reach `deviceName=llvmpipe/lavapipe` (E3.3 forbids counting it).

**Park procedure:** file `doc/08_tracking/bug/venus_capset_unavailable_<date>.md`
with the exact QEMU version, virglrenderer version, `-device help` output, host
`vulkaninfo --summary` head, and the guest serial excerpt; set every E-lane key to
`blocked:<specific reason>`; update `.spipe/simpleos-screens-render-lane/state.md`
AC-9 to `parked`. **Relabeling the modeled responses in §0.4 as real, or
substituting the host SFFI ICD, is prohibited** — removing exactly that failure
mode is why this lane exists.

---

## 7. Board-runnable blocker (`.claude/rules/board-runnable.md`)

virtio-gpu is a paravirtual QEMU device and Venus is a host-renderer protocol.
There is no path by which this workstream runs on the physical dev board. Per the
rule, the gap is stated explicitly rather than left implicit.

**File this text to `doc/08_tracking/bug/simpleos_vulkan_board_gap_venus_is_qemu_only.md`:**

> ## SimpleOS Vulkan is QEMU-only: no physical-GPU driver exists
>
> **Status:** open — filed as an explicit gap, not a defect in Workstream E.
>
> Workstream E delivers Vulkan on SimpleOS via the Venus protocol carried over
> virtio-gpu (`src/os/drivers/virtio/virtio_gpu*.spl`). virtio-gpu is a
> paravirtual device implemented by QEMU; Venus command streams are executed by
> a **host** Vulkan driver through virglrenderer. Neither exists on the physical
> dev board.
>
> Running Vulkan on the board requires work that Workstream E does **not** do and
> does not imply:
> - a native PCIe/SoC GPU driver for the board's actual GPU (mode setting,
>   command submission rings, MMU/IOMMU page tables, interrupts, power);
> - a real Vulkan ICD over that driver, not a serialization proxy;
> - firmware/DT enumeration of the GPU on the board's boot path.
>
> **Consequence for evidence:** `simpleos_venus_board_runnable_status` is
> permanently `blocked:qemu-only-virtio-gpu` for this lane. No E1-E4 evidence key
> may be read as a board claim. Any board Vulkan claim requires board identity,
> a download/boot transcript, and a serial/SSH capture from the board itself
> (board evidence bar, `.claude/rules/board-runnable.md`).
>
> **Scope decision:** the user/plan scoped this workstream QEMU-first
> (`doc/05_design/os/desktop/screen_backend_selection_and_shared_showcase.md` §2.6,
> "QEMU-only scope"). This file records that the board path is knowingly deferred.

---

## 8. Traps (repo hazards that will silently fake a pass)

1. **Unregistered `@extern fn` returns nil silently under JIT.** New externs added
   for ring fences / MMIO barriers that are not registered in the runtime return
   nil with no error. Ring cursors read as 0 forever ⇒ a wait loop that "succeeds"
   instantly. Prove each new extern by making it return a value that would be
   impossible if unregistered (a nonzero magic), then assert on it.
2. **A modeled response that returns plausible values is the exact failure this
   lane removes.** `_venus_transport_send` (:52) returns `is_ok: true` and a
   monotonically increasing handle — indistinguishable from success at every call
   site. Delete the function; do not leave it behind a flag.
3. **Evidence must be captured from a live boot, not asserted.** Every `pass` must
   be greppable out of a serial log / screendump / `.rdc` file on disk, with the
   file path recorded. A wrapper that prints `pass` from its own control flow is
   fail-open.
4. **`RESP_OK_NODATA` proves parsing, not execution.** The device acks a
   `SUBMIT_3D` header before the renderer touches the stream. Require the ring
   `tail` to advance (E2.6).
5. **Native-codegen Dict pitfalls** (`.claude/rules/code-style.md`): never call
   `Dict.len()` (returns -1) and never `.get()` a dict whose value is a
   struct/class/enum (corrupt/segfault). Capset tables and handle maps are exactly
   this shape — use `keys().len()` and `contains_key(k)` + `d[k]`.
6. **`SIMPLE_EXECUTION_MODE=native` is not a mode**; anything but `interpret` is
   JIT. Driver code must be validated on the deployed native SimpleOS build, not
   inferred from a host JIT run.
7. **Boxed vs raw memory accessors diverge.** `virtio_gpu_regs.spl` exposes both
   `ram_read32` (:94, boxed) and `ram_read32_raw` (:121). Ring cursors and MMIO
   must use the raw/real variants; a boxed read on device memory is not a
   guaranteed single-width load.
8. **`-display none` disables the GL renderer.** A headless run with `-display
   none` will report no Venus capset and read as a genuine E1 failure. Use
   `egl-headless,gl=on`.
9. **Legacy PCI transport cannot do Venus.** `virtio_gpu_init.spl:142-144` and
   `:241-243` are legacy paths that zero guest features; if the driver falls back
   there, 3D silently never negotiates. E1.2 must make that fallback an explicit
   refusal for the Vulkan lane.
10. **Host oracle contamination.** `src/compiler_rust/runtime/src/vulkan*` runs on
    the host loader. If the guest test links or dispatches into it (via
    `vulkan_icd_sffi.spl`), the checksum will match trivially and prove nothing.
    Assert `simpleos_venus_icd=virtio` in the same run that emits the checksum.
11. **Concurrent test runs race a shared manifest** — use `--no-cache
    --no-cover-check` for any spec run added by this workstream.
