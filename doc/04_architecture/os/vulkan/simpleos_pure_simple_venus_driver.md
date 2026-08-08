<!-- codex-architecture -->
# Supplemental MDSOC review: SimpleOS pure-Simple Venus protocol

Status: protocol supplement, 2026-08-08; no implementation or live-device
claim.  The accepted interface freeze is
`doc/04_architecture/simpleos_venus_gpu_stack.md`; this document introduces no
alternate classes, structs, or public interfaces.

## MDSOC confirmation

The frozen tree is the correct MDSOC split:

```text
GpuAccelerationProvider
  -> VirtioGpuDiscoveryProvider
    -> _Venus/{protocol,queue,fence,readback}
      -> existing VulkanCompositorBackend
```

`GpuProviderCapabilityReceipt` and `GpuExecutionReceipt` are the shared common
tree nodes.  `VirtioGpuPciCapability`, `VirtioGpuDeviceConfig`,
`VirtioGpuSharedMemoryRegion`, and `VirtioGpuDiscoveryReceipt` are public to
the immediate Venus layer only.  `VenusCapsetTuple`, `VenusProtocolProbe`, and
`VenusSession` are next-layer-private; `VenusCommandQueue`,
`VenusFenceReceipt`, and `VenusDeviceReadbackReceipt` are session-private.
The compositor may consume immutable execution receipts only.  It must neither
import raw virtio code nor retain a mapping, blob, queue, or fence pointer.

| Raw layer | Common / extracted node | Parent-public | Next-layer public |
|---|---|---|---|
| discovery | `GpuProviderCapabilityReceipt` | discovery receipt | Venus protocol only |
| `_Venus/protocol` | `VenusCapsetTuple` | probe/session | queue/fence/readback only |
| `_Venus/queue` | `GpuExecutionReceipt` | correlated submit result | compositor only |
| compositor | `GpuAccelerationProvider` | backend selection | no transport exposure |

## Protocol corrections to carry into frozen files

- Negotiate VIRGL, RESOURCE_BLOB, and CONTEXT_INIT before classifying a Venus
  candidate.  A discovered static id is diagnostic, never proof.
- Capset payload is host-controlled.  The frozen 4072-byte limit follows the
  current 4096-byte response buffer and must be checked before decode; capset
  count is limited to 64 and PCI capability visits to 48.
- `virtio_gpu_ctrl_hdr` includes `ring_idx`.  Any future ring fence sets fence
  and info-ring-index flags and uses the actual ring index; otherwise it must
  fail closed rather than claim a timeline receipt.
- The host-visible blob map derives from PCI SHM id 1, with 64-bit BAR extent
  containment and overflow validation.  Mapping a generic RAM/blob address is
  invalid.
- Venus capset bytes negotiate version/features; guest code supplies ring
  geometry using the exact generated upstream protocol.  The current fabricated
  `vulkan_icd_virtio.spl` opcodes are forbidden as an implementation reference.

## Boundaries and budgets

The frozen limits stand: discovery 250 ms, negotiation 500 ms, three
config-generation retries, 48 PCI visits, 64 capsets, and payload ≤4072 bytes.
Future execution uses a bounded three-frame command queue.  Setup happens once;
warm frames allocate no framebuffer and readback is capture-only.  A timeout,
malformed response, protocol mismatch, device loss, or mismatched fence
invalidates the session and leaves Vulkan unavailable.  Counters must report
setup/negotiation time, capset count/bytes, in-flight high water, fence timeout,
device loss, readbacks, and explicit fallback selection.

## Non-goals

No complete host-loader ICD, Linux DRM/ioctl port, Mesa port, WSI, arbitrary
Vulkan/shader support, CPU-as-device evidence, or physical-board GPU claim.
All successful transport evidence carries `qemu_only` until a different native
board GPU provider implements the common contract.
