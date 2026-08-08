# SimpleOS Venus GPU stack agent tasks

Interfaces are frozen in `doc/04_architecture/simpleos_venus_gpu_stack.md`.
Sidecars must use those names and may not introduce alternate providers,
renderers, event routers, or evidence schemas.

| Lane | Owned files | Deliverable | May run now |
|---|---|---|---|
| A: common provider | `src/lib/common/gpu/acceleration_provider.spl`, focused unit spec | public capability and immutable execution receipt | yes |
| B: PCI/device config | `src/os/drivers/virtio/virtio_gpu_discovery.spl`, `virtio_gpu_regs.spl`, focused unit spec | bounded DEVICE_CFG/shmem parsing and receipt | yes |
| C: capset integration | `virtio_gpu_capset.spl`, `virtio_gpu_init.spl`, focused specs | bounded complete/partial tuple walk | after B |
| D: Venus protocol | `src/os/drivers/virtio/_Venus/protocol.spl` | authoritative classifier/session handshake | after live tuples and upstream source review |
| E: blob/ring | `_Venus/blob.spl`, `_Venus/ring.spl` | host-visible blob and guest-authored ring | after D |
| F: queue/fence/readback | `_Venus/queue.spl`, `fence.spl`, `readback.spl` | device execution evidence | after E |
| G: compositor | existing `vulkan_compositor_backend.spl` and Engine2D tests | enable only from valid readback receipt | after F |
| H: QEMU evidence | canonical QEMU wrapper/spec/manual only | boot, identity, submit, fence, readback, frame checksum | after G |
| I: trace schema | `src/lib/common/spec/differential_trace.spl`, focused spec | immutable normalized records and bounded injected sink | after interface review |
| J: comparator/profile | `test/helpers/differential_conformance.spl`, focused specs | semantic projection, handle mapping, GPU profiles | after I |
| K: Mesa/Vulkan SFFI oracle | `src/lib/nogc_sync_mut/gpu/reference_oracle_sffi.spl`, `test/helpers/gpu_reference_oracle.spl`, compiled specs | dynload ABI/error/ownership and normalized trace | after I; test-only |
| L: Chrome/Web consumer | existing Web performance test helpers/specs only | adopt generic trace/comparator without GPU imports | after J |

Lower-model sidecars: lanes A, B, and pure test-gap inventory are suitable for
Codex Luna/Claude Haiku after slots are available. Protocol classification and
all completion claims require normal/highest-capability review. Merge owner:
`/root`. Final reviewer: `/root` normal/highest-capability verifier.

Shared manual helper names: `inspect_bounded_device_capabilities`,
`enumerate_capset_tuples`, `confirm_discovery_only_admission`,
`submit_and_fence_drawir_frame`, `readback_and_correlate_device_pixels`.
The last two remain explicit fail-fast placeholders until implemented.
