<!-- codex-research -->
# SimpleOS Venus GPU stack: domain research

Status: primary-source architecture summary, 2026-08-08.

## Normative transport facts

The OASIS VirtIO 1.3 specification defines device configuration as
`VIRTIO_PCI_CAP_DEVICE_CFG` and shared-memory regions as repeated
`VIRTIO_PCI_CAP_SHARED_MEMORY_CFG` capabilities using `virtio_pci_cap64`.
The capability ID distinguishes regions; offset and length are 64-bit pairs,
and the advertised region must be contained in its BAR. Drivers must ignore
reserved capability types/BARs, accept larger capability lengths, and map only
the portion required for operation.

For virtio-gpu, `virtio_gpu_config` exposes `num_capsets` at byte offset 12.
The host-visible shared-memory region has shmid 1. Its presence requires
RESOURCE_MAP_BLOB/RESOURCE_UNMAP_BLOB support, but presence alone does not
prove Venus, Vulkan execution, or readable rendered pixels.

Primary references:

- [OASIS VirtIO 1.3](https://docs.oasis-open.org/virtio/virtio/v1.3/virtio-v1.3.html), sections 2.10, 4.1.4, and 5.7.
- [Linux `virtio_pci.h`](https://github.com/torvalds/linux/blob/master/include/uapi/linux/virtio_pci.h), the `virtio_pci_cap`/`virtio_pci_cap64` layouts and capability IDs.
- [Linux `virtio_gpu.h`](https://github.com/torvalds/linux/blob/master/include/uapi/linux/virtio_gpu.h), GPU configuration, capset commands, blob/map commands, fencing, and shmid values.

## Venus architecture facts

The in-repo primary-source audit records that a Venus capset is a protocol
version/feature handshake, not a ring-layout descriptor. Ring geometry is
guest-owned and later declared with the real Venus protocol. Therefore this
slice may enumerate and retain capset tuples and bounded payload bytes, but it
must not invent ring fields or treat a tuple as executable Vulkan.

The future ordering is: typed-context creation, host-visible blob creation and
mapping, guest-authored ring creation, serialized Vulkan submission, fence
completion, and device-origin readback. Exact Venus serialization must come
from Mesa/virglrenderer source before implementation; the fabricated opcode
model in `src/lib/nogc_async_mut/gpu/vulkan_icd_virtio.spl` is explicitly not a
protocol reference.

Primary project references to the upstream review:

- `doc/01_research/os/vulkan/venus_virtio_gpu_protocol_facts.md`
- [Mesa Venus documentation](https://docs.mesa3d.org/drivers/venus.html)
- [Mesa source](https://gitlab.freedesktop.org/mesa/mesa/-/tree/main/src/virtio/vulkan)
- [virglrenderer source](https://gitlab.freedesktop.org/virgl/virglrenderer)

## Consequence for evidence

Configuration and tuple discovery are Ready-class facts. A Vulkan Pass needs
an actual device identity, successful command submission, known fence
completion, a positive backend handle, device-origin readback, a correlated
frame identity/checksum, exact CPU-oracle parity, and `fallback_used=false`.

## Differential oracle and VUDA review (2026-08-08 addendum)

Mesa's Venus implementation and virglrenderer are protocol references and may
be executed through a dynamically loaded, test-only Vulkan/Mesa adapter as a
differential oracle. The adapter compares normalized semantic events; it is
not linked into SimpleOS, is not a production fallback, and cannot confer
availability on the pure-Simple provider. Vulkan handles, addresses, raw
timestamps, allocator choices, and implementation-private command ordering are
not equality fields.

[VUDA](https://github.com/jgbit/vuda) is a header-only C++ CUDA Runtime-style
facade that owns Vulkan devices, allocation, copying, and SPIR-V kernel launch.
That application API does not implement VirtIO DEVICE_CFG/capset discovery,
the Venus wire protocol, guest rings/fences, or the frozen provider receipts.
Decision: do not migrate or vendor it; deprecate it as a proposed production
route. A separately obtained VUDA binary may only remain an explicitly
external compute-test reference, never the Mesa/Vulkan conformance oracle or
the SimpleOS render path. No upstream source is copied.
