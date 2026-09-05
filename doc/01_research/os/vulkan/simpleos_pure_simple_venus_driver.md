<!-- codex-research -->
# SimpleOS pure-Simple Venus driver: domain research

Status: primary-source research, design-only, 2026-08-08.

## Grounded external facts

- The [VirtIO 1.2 GPU specification](https://docs.oasis-open.org/virtio/virtio/v1.2/virtio-v1.2.html)
  defines virtio-gpu as 2D/3D, with controlq and cursorq; control requests and
  responses have a fixed header followed by command data.  It defines VIRGL,
  RESOURCE_BLOB, and CONTEXT_INIT; CONTEXT_INIT requires VIRGL.  Therefore the
  session must negotiate all relevant offered bits before it tries capsets.
- [Mesa Venus documentation](https://docs.mesa3d.org/drivers/venus.html) calls
  Venus a virtio-gpu protocol for Vulkan command serialization, points to its
  generated protocol/codegen and virglrenderer, and lists 3D features, capset
  query fix, resource blob, host-visible memory, and context init as required
  guest-kernel capabilities.  A host render node is consequently insufficient
  proof of Venus support.
- The [Khronos loader/driver interface](https://github.com/KhronosGroup/Vulkan-Loader/blob/main/docs/LoaderDriverInterface.md)
  defines loader/driver negotiation and dispatch discovery for a host shared
  library ICD.  That ABI is not an in-kernel transport contract.  SimpleOS
  should first expose a pure-Simple provider facade; a native loader-compatible
  ICD is a later, separately scoped adapter once platform dynamic loading and
  ABI safety exist.
- The [Vulkan registry](https://github.com/KhronosGroup/Vulkan-Docs) is the
  source from which headers and API descriptions are generated.  Real Venus
  serialization must be generated or mechanically pinned to the matching
  upstream protocol/version, never hand-written from a subset of public Vulkan
  entry points.

## Consequences

The first implementation is neither a Linux DRM driver nor a complete Vulkan
ICD.  It is a QEMU-scoped guest transport capsule that proves: negotiated
features → discovered/validated capset → mapped host-visible blob → real,
version-matched Venus ring setup → fenced command → device-origin readback.
If any link is absent, it returns an explicit error and leaves the existing CPU
or rejecting backend selected.  This is compatible with upstream architecture
without importing its Linux, C, ioctl, or dynamic-loader assumptions.

## Non-goals

- No fabricated Venus opcode compatibility layer.
- No guest Linux DRM/ioctl emulation, Mesa port, shader compiler, WSI surface,
  general application-facing ICD, arbitrary shader execution, or board-GPU
  claim.
- No Vulkan availability based on `/dev/dri` existence, environment flag,
  static capset id, host-side screenshot, or CPU-generated pixels.
