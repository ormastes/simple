<!-- codex-research -->
# SimpleOS Venus GPU stack: local research

Status: interface-freeze research, 2026-08-08. This document does not claim a
live Venus device, Vulkan command execution, or device-origin readback.

## Existing implementation

The repository already has one canonical 2D virtio-gpu driver capsule:
`src/os/drivers/virtio/virtio_gpu.spl`, with initialization in
`virtio_gpu_init.spl`, drawing/display commands in `virtio_gpu_ops.spl`, wire
constants in `virtio_gpu_types.spl`, and feature/capset work in
`virtio_gpu_capset.spl`. It must be extended; a second GPU driver or renderer
would violate the Simple2D architecture.

Implemented and unit-tested today:

- modern common/notify/ISR PCI-capability discovery;
- low-word VIRGL, RESOURCE_BLOB, and CONTEXT_INIT feature negotiation;
- GET_CAPSET_INFO/GET_CAPSET encoders and response decoding;
- a controlq walk whose capset count is passed by the caller;
- the fail-closed `VulkanCompositorBackend`, which rejects all drawing because
  no Venus session or device readback exists.

The architectural gap is explicit in `virtio_gpu_capset.spl`: the driver does
not map `VIRTIO_PCI_CAP_DEVICE_CFG`, so it cannot read
`virtio_gpu_config.num_capsets`; it also does not parse the 64-bit shared-memory
PCI capability for `VIRTIO_GPU_SHM_ID_HOST_VISIBLE`. Existing capset ID 4 is a
speculative constant in this tree. It is not live device evidence.

## Existing boundaries and defects

- `VirtioGpuDriver.try_map_modern_pci_caps` walks an unbounded capability chain
  and only stores common, notify, and ISR windows.
- Capability BAR addresses are treated as directly usable MMIO addresses. A
  future mapper must validate BAR extent and overflow before admitting them.
- `gpu_query_capsets` accepts an unbounded caller count and returns a partial
  list on the first failure, without a typed partial/failure receipt.
- The shared 4096-byte response buffer bounds a capset payload to 4072 bytes;
  `gpu_get_capset` does not currently enforce that bound.
- `vulkan_compositor_backend.spl` is correctly unavailable and must remain so
  until a real queue submit, fence, identity, and device-origin readback pass.

## Reusable seams

- `DeviceGrant` owns PCI identity and BAR0 authority.
- `VirtioGpuDriver` owns PCI/config/controlq/device lifetime.
- `GpuCapset` is the existing capability tuple `(id, max_version, max_size)`.
- `DrawIrComposition` and Engine2D remain the only compositor execution path.
- `UiEnvironmentEvidence` already separates Ready from live guest Pass.

## Required first slice

Extend the existing driver with bounded PCI capability discovery, typed
DEVICE_CFG and host-visible shared-memory facts, a bounded capset table receipt,
and a Venus-candidate tuple. Stop before CTX_CREATE, blobs, command rings,
SUBMIT_3D, fences, or rendering. This is discovery evidence only.

Related documents:

- `doc/01_research/os/vulkan/venus_virtio_gpu_protocol_facts.md`
- `doc/04_architecture/os/vulkan/simpleos_vulkan_render_backend_plan.md`
- `doc/04_architecture/simple2d_primitive_lane.md`
- `doc/08_tracking/bug/simpleos_vulkan_board_gap_venus_is_qemu_only.md`
