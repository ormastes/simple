# Vulkan on SimpleOS is QEMU-only: Venus has no physical-board path

- **Filed:** 2026-08-06
- **Status:** OPEN — blocker, parked
- **Area:** `src/os/drivers/virtio/virtio_gpu*.spl`, WS-E (Venus/Vulkan)
- **Plan:** `doc/03_plan/os/simpleos/screens/ws_e_vulkan_detail.md` §7
- **Rule invoked:** `.claude/rules/board-runnable.md` — a QEMU-only result is a
  defect, not a completion, and must be filed explicitly rather than shipped
  with an implied board claim.

## 1. The architectural gap (permanent, not a host issue)

Venus is **not a GPU driver**. It is a Vulkan *command-forwarding protocol*: the
guest serializes Vulkan calls into a virtio-gpu context ring, and a **host**
`virglrenderer` process deserializes them and replays them against the **host's**
Vulkan driver. virtio-gpu itself is a paravirtual PCI device.

Therefore:

- On a physical dev board there is **no host** to forward to. There is no
  virtio-gpu device on the PCI bus, and nothing implements the other end of the
  ring.
- Making Vulkan work on the board is a **completely disjoint** work item from
  WS-E: it requires a native KMS/DRM driver plus a real Vulkan implementation
  for the board's actual GPU IP (e.g. Mali/Adreno/Imagination). None of that is
  in scope for, or shares code with, the Venus transport.
- No amount of WS-E1..E4 work moves the board forward. WS-E must therefore never
  be reported as a step toward board Vulkan.

**Consequence for evidence rows:** every WS-E result must carry
`platform=qemu`. A WS-E row must never be cited as board-runnable, and the
absence of a board path here is by design of the protocol, not a temporary gap.

## 2. This host additionally cannot run Venus in QEMU either

Even the QEMU-only path is blocked on this machine, so E1 could not be proven
live. Measured 2026-08-06:

| Check | Result |
|---|---|
| `vulkaninfo --summary` | **works** — NVIDIA TITAN RTX + NVIDIA RTX A6000 (Vulkan 1.4.312), plus `llvmpipe` |
| `qemu-system-x86_64 --version` | 8.2.2 (Debian `1:8.2.2+ds-0ubuntu1.17`) |
| `-device help \| grep virtio-gpu` | lists `virtio-gpu-gl-pci` / `virtio-gpu-gl-device` |
| **instantiating it** | **FAILS** |
| `qemu-system-riscv64 -device virtio-gpu-gl-pci,help` | same failure (the plan targets a riscv64 guest) |
| virglrenderer | `libvirglrenderer.so.1.8.8`; `nm -D \| grep -i venus` → **empty** |

Two **independent** blockers, either one of which is fatal:

**(a) The GL device module is unloadable.**
```
$ qemu-system-x86_64 -device virtio-gpu-gl-pci,help
qemu-system-x86_64: -device virtio-gpu-gl-pci,help: failed to open module:
  /usr/lib/x86_64-linux-gnu/qemu/hw-display-virtio-gpu-gl.so:
  undefined symbol: qemu_egl_display

$ qemu-system-x86_64 -display none -device virtio-gpu-gl-pci
qemu-system-x86_64: -device virtio-gpu-gl-pci: opengl is not available
```
The device *appears* in `-device help` because that lists modules by filename,
but the shared object references `qemu_egl_display`, which the packaged
`qemu-system-*` binary does not export (`ldd qemu-system-x86_64 | grep -c
libEGL` → 0). **No `-display` flag can work around this** — the failure is at
module load, before any display backend is selected. In particular this is *not*
the `-display none` false-negative described in the plan; `egl-headless` and
`sdl,gl=on` fail identically.

**(b) Neither QEMU 8.2.2 nor virglrenderer 1.8.8 supports Venus.**
- `strings hw-display-virtio-gpu-gl.so` contains **no** `venus`, `blob` or
  `context_init` property name. QEMU gained the `venus=` device property in
  **9.1**; 8.2.2 predates it, so the plan's
  `-device virtio-gpu-gl-pci,hostmem=256M,blob=true,venus=true,context_init=true`
  would be rejected as an unknown property even if (a) were fixed.
- `libvirglrenderer.so.1.8.8` exports **no** venus symbols. The sole `venus`
  hit in its strings is `VK_MESA_venus_protocol`, a Mesa extension **name** in a
  table — not an implementation. It was not built `-Dvenus=true`.

Note also that `llvmpipe` is present in `vulkaninfo`. Per the lane's honesty
rules, any future run that lands on llvmpipe/lavapipe is
`blocked:software-renderer`, **never** `pass`.

## 3. What E1 shipped anyway, and what it does NOT claim

The E1 code is implemented and unit-tested offline:

- `src/os/drivers/virtio/virtio_gpu_types.spl` — device feature bits, the
  `0x0108`/`0x0109` capset opcodes, the remaining 3D/blob opcodes, responses
  `0x1102`/`0x1103`/`0x1106`, capset struct sizes and field offsets.
- `src/os/drivers/virtio/virtio_gpu_capset.spl` — `gpu_negotiate_features` plus
  pure wire encode/decode, and the device-side capset walk.
- `src/os/drivers/virtio/virtio_gpu_init.spl` — the modern path now ACKs
  `host_features & (VIRGL|RESOURCE_BLOB|CONTEXT_INIT)` instead of writing 0. The
  legacy paths keep writing 0 and set `has_3d/has_blob/has_ctx_init = false`
  **deliberately** — legacy PCI cannot carry Venus.
- `test/01_unit/os/drivers/virtio/virtio_gpu_capset_spec.spl` — offline specs.

**Explicitly NOT claimed:**

- **No live capset was ever queried.** No capset id, max_version or max_size has
  been observed from a running device.
- **No Venus capset id is asserted anywhere.** An earlier draft of this work
  hardcoded `VIRTIO_GPU_CAPSET_VENUS = 4`. **That was a fabrication and has been
  removed.** `/usr/include/linux/virtio_gpu.h:310-311` defines exactly two capset
  ids — `VIRGL = 1` and `VIRGL2 = 2` — and **no Venus constant**. The Venus id is
  not established by any citable source available here. The code therefore
  locates Venus by *enumeration* (`gpu_candidate_venus_capsets` returns any
  discovered id that is not one of the two known virgl ids, as a **candidate**)
  and never by comparison against a guessed constant. Confirming a candidate
  requires the GET_CAPSET version handshake, which needs a live device.

### 3a. Protocol corrections folded in from the header audit

Verified verbatim against `/usr/include/linux/virtio_gpu.h` on this host:

- `VIRTIO_GPU_SHM_ID_HOST_VISIBLE` is **1, not 0** (`:127`); 0 is `UNDEFINED`.
  Recorded in `virtio_gpu_types.spl`.
- The ctrl-header's byte at **offset 20 is `ring_idx`, a real field** (`:142`),
  not padding, and `VIRTIO_GPU_FLAG_INFO_RING_IDX` is `1 << 1` (`:135`). Without
  setting both, every Venus fence is attributed to ring 0 regardless of which
  ring did the work. The 2D path never sets the flag, so its existing zero write
  at offset 20 stays correct — but E2 must handle this. Both the corrected
  layout comment and the two flag constants are now in `virtio_gpu_types.spl`.
- `VIRTIO_GPU_CONTEXT_INIT_CAPSET_ID_MASK = 0x000000ff` (`:283`) added.

Two plan assumptions are **unimplementable as written** and must be fixed before
E2 starts (not fixed here, since E2 is out of scope for this run):

- *"Parse the ring layout from the capset blob"* — the Venus capset carries **no
  ring layout**. It is a version/feature handshake only. Ring geometry is
  guest-authored and declared to the host via `vkCreateRingMESA` over
  `SUBMIT_3D`. What the capset read actually gates is `supports_blob_id_0`,
  needed to create the ring shmem with `blob_id=0`.
- *`BLOB_MEM_GUEST` as an "E2 minimum viable" milestone* — a dead end, not a
  smaller step. The Venus ring must be host-visible (`HOST3D` + `MAP_BLOB`).

### 3b. Fabricated-opcode trap in the modeled ICD

`src/lib/nogc_async_mut/gpu/vulkan_icd_virtio.spl:42-46` defines
`VENUS_OP_CREATE_INSTANCE = 1` … `VENUS_OP_DESTROY_INSTANCE = 5`. **These are
invented stub opcodes for the modeled transport — they are NOT the Venus
protocol.** Real Venus command ids come from the `venus_protocol`
`VkCommandTypeEXT` encoding. A future implementer will grep for "VENUS_OP",
find these, and trust them. That file was deliberately not edited in this run
(it is E3 scope); the trap is recorded here and in the header comment of
`virtio_gpu_capset.spl` so it cannot be adopted silently.
- E2 (ring transport) and E3 (ICD rewiring) are untouched.
  `src/lib/nogc_async_mut/gpu/vulkan_icd_virtio.spl` remains **fully modeled**
  and must not be described as real until a transport exists.

## 4. Secondary defect noticed while implementing E1

The driver maps only the virtio-pci **common**, **notify** and **isr**
capabilities (`virtio_gpu.spl:275-283`) — there is **no `VIRTIO_PCI_CAP_DEVICE_CFG`
accessor**. So `virtio_gpu_config.num_capsets` (device-config offset 8) cannot be
read. Reading offset 8 through the existing `modern_read32` would hit the
**common-cfg** window and return a `device_feature` field — a plausible-looking
wrong number.

E1 therefore takes `num_capsets` as an explicit parameter to
`gpu_query_capsets(drv, num_capsets)` rather than fabricating it. Wiring a
DEVICE_CFG accessor is E2 work and is tracked here.

## 5. Unblocking conditions (all required, QEMU path only)

1. QEMU **≥ 9.1** built `--enable-opengl --enable-virglrenderer`, with the
   `hw-display-virtio-gpu-gl` module resolving `qemu_egl_display`.
2. virglrenderer **≥ 0.10** built `-Dvenus=true` (verify: `nm -D` shows venus
   symbols, not just the `VK_MESA_venus_protocol` string).
3. A host Vulkan 1.2+ **hardware** driver — satisfied here (NVIDIA), but a run
   that falls back to llvmpipe is `blocked:software-renderer`.
4. `-display sdl,gl=on` or `egl-headless,gl=on`. **Never `-display none`** — it
   disables the GL renderer and reads as a false E1 failure.
5. Guest args: `-device virtio-gpu-gl-pci,hostmem=256M,blob=true,venus=true,context_init=true`
   (x86_64/aarch64 variant: `-device virtio-vga-gl,blob=true,venus=true`).

Until 1 and 2 hold on some machine, E1 cannot be proven live and WS-E stays
parked. **For the board, no unblocking condition exists** — see §1.
