# Venus / virtio-gpu 3D protocol facts (for Workstream E, task E2.4 review)

Date: 2026-08-06. Resolves the open review item on
`doc/03_plan/os/simpleos/screens/ws_e_vulkan_detail.md` E2.4.

**Primary source found on this host:** `/usr/include/linux/virtio_gpu.h`
(Linux uapi, 11454 bytes, dated 2025-07-01). Everything cited below with a
`virtio_gpu.h:N` reference is copied from that file, not recalled. No
virglrenderer (`virgl_hw.h`), Mesa (`venus_hw.h`), or crosvm source exists on
this host or anywhere in this repo — so every **Venus-specific** value is
recollection and is rated accordingly.

## Headline finding (the E2.4 item)

**The Venus capset does not contain a ring layout. There is no field to parse.**
`virgl_renderer_capset_venus` is a version/feature handshake
(`wire_format_version`, `vk_xml_version`, protocol spec-version fields,
`supports_blob_id_0`, …). The Venus ring geometry is **guest-authored**: the
driver picks the offsets and sizes inside a host-visible blob and *declares* them
to the host with a `vkCreateRingMESA` command sent over `SUBMIT_3D`.

So E2.4's "parse it, never hardcode" is unimplementable as written — but the
instinct is not wrong, just misaimed: the capset **must** still be read, because
`supports_blob_id_0` is what gates creating the ring shmem with `blob_id = 0`.

## 1. Feature bits — HIGH (all cited)

| Name | Bit | Cite |
|---|---|---|
| `VIRTIO_GPU_F_VIRGL` | 0 | virtio_gpu.h:47 |
| `VIRTIO_GPU_F_EDID` | 1 | virtio_gpu.h:52 |
| `VIRTIO_GPU_F_RESOURCE_UUID` | 2 | virtio_gpu.h:56 |
| `VIRTIO_GPU_F_RESOURCE_BLOB` | 3 | virtio_gpu.h:61 |
| `VIRTIO_GPU_F_CONTEXT_INIT` | 4 | virtio_gpu.h:66 |

Plan lines 135-139 are **correct**. Required for Venus: `RESOURCE_BLOB` and
`CONTEXT_INIT` (both HIGH — without them there are no blobs and no capset-typed
context). `VIRGL` gates the 3D command range in practice on QEMU, so requiring it
is safe, but "Venus strictly requires bit 0" is MEDIUM.

## 2. Capset discovery — struct layouts HIGH, Venus id MEDIUM

`struct virtio_gpu_ctrl_hdr` (virtio_gpu.h:137) = **24 bytes**:
`le32 type; le32 flags; le64 fence_id; le32 ctx_id; u8 ring_idx; u8 padding[3]`.

**Note `ring_idx` — it is a real field, not padding.** The plan's header model
omits it. See §5.

| Struct | Layout | Size | Cite |
|---|---|---|---|
| `virtio_gpu_get_capset_info` | hdr + `le32 capset_index` + `le32 padding` | 32 | :314 |
| `virtio_gpu_resp_capset_info` | hdr + `le32 capset_id, capset_max_version, capset_max_size, padding` | 40 | :321 |
| `virtio_gpu_get_capset` | hdr + `le32 capset_id` + `le32 capset_version` | 32 | :330 |
| `virtio_gpu_resp_capset` | hdr + `u8 capset_data[]` | 24+var | :337 |

Plan lines 151-153 are **correct**, including the two 32/40 sizes.

Commands: `GET_CAPSET_INFO = 0x0108`, `GET_CAPSET = 0x0109` (sequential from
`0x0100`, virtio_gpu.h:80-81) — HIGH. `RESP_OK_CAPSET_INFO = 0x1102`,
`RESP_OK_CAPSET = 0x1103` (:106-107) — HIGH.

Capset ids in uapi: **only** `VIRTIO_GPU_CAPSET_VIRGL 1` and
`VIRTIO_GPU_CAPSET_VIRGL2 2` (virtio_gpu.h:310-311). **`VENUS` is not in the
uapi header.** My recollection is `VENUS = 4` (after `GFXSTREAM = 3`), but it
lives in virglrenderer/Mesa/crosvm and I cannot cite it → **MEDIUM**. E2 keys
`ctx_create.context_init` off this value, which is the worst place for a guess.
**Instruction for E2: never hardcode the id.** Enumerate `num_capsets` from the
device config, issue `GET_CAPSET_INFO(i)` for each, log every
`(id, max_version, max_size)` triple, and match the discovered id.

Venus capset v0 payload fields: MEDIUM for the first four
(`wire_format_version`, `vk_xml_version`,
`vk_ext_command_serialization_spec_version`,
`vk_mesa_venus_protocol_spec_version`), LOW past that. HIGH only on the negative
claim: **no ring offsets, no ring size**.

## 3. `CTX_CREATE` with context_init — HIGH

`VIRTIO_GPU_CMD_CTX_CREATE = 0x0200` (virtio_gpu.h:88).
`struct virtio_gpu_ctx_create` (:284) = hdr + `le32 nlen` + `le32 context_init`
+ `char debug_name[64]` = **96 bytes**.
`VIRTIO_GPU_CONTEXT_INIT_CAPSET_ID_MASK = 0x000000ff` (:283) — the capset id
goes in the low 8 bits of `context_init`. Plan lines 266-273 **correct**.

## 4. Blob resources — HIGH

`RESOURCE_CREATE_BLOB = 0x010c`, `SET_SCANOUT_BLOB = 0x010d`,
`RESOURCE_MAP_BLOB = 0x0208`, `RESOURCE_UNMAP_BLOB = 0x0209`,
`RESP_OK_MAP_INFO = 0x1106` — all sequential-enum derived, HIGH.

`virtio_gpu_resource_create_blob` (:394) = hdr + `le32 resource_id, blob_mem,
blob_flags, nr_entries` + `le64 blob_id` + `le64 size` = **56 bytes**, followed
by `nr_entries` × `virtio_gpu_mem_entry` (`le64 addr; le32 length; le32 padding`
= 16 B each). Plan line 288-289 **correct**.

`BLOB_MEM_GUEST 0x0001`, `HOST3D 0x0002`, `HOST3D_GUEST 0x0003` (:397-399).
`BLOB_FLAG_USE_MAPPABLE 0x0001`, `USE_SHAREABLE 0x0002`, `USE_CROSS_DEVICE
0x0004` (:401-403). Plan lines 283-286 **correct**.

`virtio_gpu_resource_map_blob` (:430) = hdr + `le32 resource_id` + `le32 padding`
+ `le64 offset` = 40 B. `virtio_gpu_resp_map_info` (:443) = hdr + `u32 map_info`
+ `u32 padding`; `map_info & VIRTIO_GPU_MAP_CACHE_MASK(0x0f)` ∈ {NONE 0, CACHED
1, UNCACHED 2, WC 3} (:438-442).

**`VIRTIO_GPU_SHM_ID_HOST_VISIBLE = 1`** (virtio_gpu.h:127; `UNDEFINED = 0`).
The `offset` in `MAP_BLOB` is an offset into that shared-memory region, located
via the PCI shared-memory capability with shmid **1**. If any E2 code assumes
shmid 0, it will map the wrong region.

## 5. Venus ring / transport

- Fencing: `VIRTIO_GPU_FLAG_FENCE = (1<<0)` (:130) and
  **`VIRTIO_GPU_FLAG_INFO_RING_IDX = (1<<1)`** (:135) — "if set, `ring_idx`
  contains the index of the command ring used when creating the fence". Both
  HIGH. Venus uses per-ring timelines, so a fence on a Venus ring needs
  `FLAG_FENCE | FLAG_INFO_RING_IDX` **and** `hdr.ring_idx` set. The plan's E2.5
  (line 331-335) sets only `FLAG_FENCE` → fences land on ring 0 regardless of
  which ring the work went to. **This is a plan defect.**
- `SUBMIT_3D = 0x0207`; `virtio_gpu_cmd_submit` (:305) = hdr + `le32 size` +
  `le32 padding` = 32 B, cmd-stream bytes follow. Plan line 333 **correct**.
- Bring-up order (MEDIUM): CTX_CREATE(capset=venus) → RESOURCE_CREATE_BLOB
  (`HOST3D`, `blob_id=0`, `USE_MAPPABLE`) → RESOURCE_MAP_BLOB → SUBMIT_3D a
  `vkCreateRingMESA` carrying the guest-chosen layout → subsequent Vulkan
  command streams go into the ring.
- `VkRingCreateInfoMESA` / Mesa `vn_ring_layout` exact field order and sizes:
  **LOW — do not implement from this document.**

## 6. Local repo: nothing authoritative, and one trap

`src/lib/nogc_async_mut/gpu/vulkan_icd_virtio.spl:42-46` defines
`VENUS_OP_CREATE_INSTANCE = 1`, `VENUS_OP_CREATE_DEVICE = 2`, … These are
**fabricated stub opcodes, not the Venus protocol.** Real Venus carries
serialized Vulkan commands, not a five-opcode enum, and the file's own
`_venus_transport_send` just increments a counter. Do not treat it as a
reference. No other owned file in the repo defines any virtio-gpu 3D constant.

## 7. Confidence summary

| Item | Rating |
|---|---|
| Feature bits 0-4 | HIGH (cited) |
| Venus requires BLOB + CONTEXT_INIT | HIGH |
| Venus strictly requires VIRGL bit | MEDIUM |
| capset info/get struct layouts + sizes | HIGH (cited) |
| `CAPSET_VIRGL 1`, `VIRGL2 2` | HIGH (cited) |
| `CAPSET_VENUS = 4` | **MEDIUM — do not hardcode** |
| Venus capset payload field list | MEDIUM (first 4) / LOW (rest) |
| Venus capset contains no ring layout | HIGH |
| `ctx_create` layout + capset-id mask | HIGH (cited) |
| blob create/map layouts, mem/flag values | HIGH (cited) |
| `SHM_ID_HOST_VISIBLE = 1` | HIGH (cited) |
| `FLAG_FENCE` / `FLAG_INFO_RING_IDX` / `ring_idx` | HIGH (cited) |
| Venus bring-up call order | MEDIUM |
| `VkRingCreateInfoMESA` field order | LOW |
| QEMU `context_init=true` device property | **LOW — unverified** |

## 8. What E2 must do differently

1. **Rewrite E2.4.** Drop "parse the ring layout from the capset" — that field
   does not exist. E2 *defines* the layout; the capset read stays, but its job is
   the version handshake and `supports_blob_id_0`.
2. **Discover the Venus capset id, never hardcode 4.** Log all triples.
3. **`BLOB_MEM_GUEST` is not a valid E2 minimum-viable path** (plan line 302).
   The Venus ring shmem must be host-visible: `BLOB_MEM_HOST3D` + `MAP_BLOB` +
   the shmid-1 region. A GUEST-only E2 cannot run Venus at all — it is a dead
   end, not a reduced milestone. This makes `pci_bar64.spl` an E2 blocker, not
   an E2-optional.
4. **Add `ring_idx` to the header struct** and set
   `FLAG_FENCE | FLAG_INFO_RING_IDX` on Venus fences.
5. **Use shmid 1**, not 0, for the host-visible region.

## 9. Must be confirmed against a live device before E2 lands

- The Venus capset id, read back from `GET_CAPSET_INFO` enumeration on a real
  `virtio-gpu-gl` with `venus=true`. Everything else in E2 hangs off this.
- The Venus capset **v0 blob size and its first 16 bytes**, hexdumped, before any
  field is named in code.
- Whether QEMU accepts `context_init=true` as a device property (plan line 206).
  **On this host `qemu-system-x86_64 -device virtio-gpu-gl-pci,help` fails to
  load the module at all: `hw-display-virtio-gpu-gl.so: undefined symbol:
  qemu_egl_display`.** E1.4's QEMU line is therefore unverified *and* the local
  QEMU cannot currently run this lane — resolve before E1, not E2.
- `RESP_OK_MAP_INFO.map_info` cache value actually returned for the ring blob.
- The exact `vkCreateRingMESA` wire encoding, from Mesa's
  `venus-protocol/vn_protocol_driver_transport.h` — fetch the real header; do
  not derive it from §5.
