# Architecture: SimpleOS Vulkan/CUDA/Adreno and Dual Knowledge Routing

## Decision

Adopt two independent composition axes.

```text
GPU session
├── VulkanDevicePort                 render/present
│   ├── QemuVulkanHostAdapter        typed host-offload evidence
│   ├── VirtioGpuVenusProtocol       exact LE wire codec + typed validation
│   │   ├── VenusEnvironment         separated discovery/admission evidence
│   │   ├── VenusPciCaps             bounded snapshot + BAR grant parser
│   │   ├── VenusControlq            bounded transport seam
│   │   └── VirtioGpuVenusAdapter    future direct guest-native evidence
│   └── AdrenoTurnipAdapter          UNO Q staged native adapter
└── ProcessingDevicePort             ProcessingIr execution
    ├── VulkanProcessingAdapter
    └── CudaHostOffloadAdapter
```

CUDA shares ProcessingIR, session correlation, invalidation, and evidence
policy with Vulkan. It does not implement Vulkan and is never named Vulkan.
Draw IR remains the rendering semantic owner; this change adds no renderer,
font path, command collector, or public platform-specific drawing API.

```text
implementation task
├── feature-group base -> exact feature expert
└── longest-prefix layer-base -> declared layer experts
    └── deterministic knowledge_selection.sdn receipt
```

Feature groups capture cross-layer intent. Layer bases capture ownership,
dependency direction, runtime constraints, and verification rules. Both are
required before design or implementation.

## MDSOC+ grouping

MDSOC grouping is hierarchical rather than limited to one small feature:

- a feature belongs to a feature group;
- related feature groups may form a domain group;
- every source path belongs to one architectural layer base;
- specialized feature and layer experts overlay their corresponding base;
- the selected group bases and overlays form a virtual capsule for the task.

This does not weaken the kernel boundary. `src/os/kernel/**` and
`src/os/drivers/**` force `mdsoc_only`. `src/os/services/**` and
`src/os/apps/**` may use MDSOC+ with an ECS business layer.

## Ports and provenance

Every execution result records backend, transport/evidence class, device and
driver identity, device handle, generation, run/frame/submission/fence/readback
IDs, checksum, mismatch count, and readback source. Admission rejects zero or
stale provenance, CPU mirrors, backend/evidence-class conflation, and missing
completion.

Evidence classes are at least `host-offload`, `guest-native`, `board-linux`,
`simpleos-native`, `software`, and `unsupported`. Promotion never crosses
classes implicitly.

## QEMU

The existing ivshmem host daemon is the selected current-host implementation.
The direct guest-native row requires a Venus-capable QEMU/virglrenderer host and
SimpleOS virtio-gpu capset, blob resource, context, fence, shared-memory, and
guest ICD support. The two rows share contracts but not completion status.

`VirtioGpuVenusProtocol` is an MDSOC-only private driver leaf beneath the
existing virtio-gpu owner. It owns protocol constants, bounded request/response
records, feature and capset admission, identifier validation, and exact packed
little-endian encoders for capset discovery, context creation, HOST3D blob
creation, fenced `SUBMIT_3D`, and fenced blob mapping. Its typed response
validator rejects truncated/error/type-mismatched headers, unknown flags,
missing or mismatched fence echoes, and unexpected fences on unfenced requests.
It does not own Vulkan semantics, Draw IR, ProcessingIR, presentation policy,
virtqueue transport, or host offload.

Protocol admission is deliberately a third state between “no Venus knowledge”
and “guest-native Vulkan.” It can establish only that a proposed transaction is
well-formed and supported by negotiated metadata. It must return a typed
blocked/unsupported result when required feature bits, capset version/size,
nonzero identifiers, bounded payloads, or prerequisite ordering are absent.
Passing this stage proves deterministic wire bytes and response correlation; it
does not create a device handle, submit a virtqueue chain, observe an interrupt,
signal a device fence, or authorize `guest-native` evidence.

The bounded implementation seam is `virtio_gpu_venus_controlq`. It may only
translate the protocol codec's request bytes into the existing virtio controlq
descriptor lifecycle and return the device-owned response bytes to the typed
validator. Queue allocation, descriptor ownership, timeout/reset invalidation,
used-ring completion, and DMA/cache lifetime remain in the existing virtio-gpu
transport owner. This seam must not parse Venus commands again or manufacture
successful responses.

`virtio_gpu_venus_environment` keeps host-offered bits, negotiated bits,
device-config capset cardinality, the enumerated Venus capset, PCI
`HOST_VISIBLE` shared memory, and capset-query-fix behavior as separate typed
observations. It admits exactly one valid Venus and host-visible row only after
the required feature mask is both offered and negotiated. This pure admission
does not authorize physical BAR access: the live PCI owner must still validate
capability lengths and cycles, use checked BAR arithmetic, and obtain a kernel
grant covering the discovered region.

`virtio_gpu_venus_pci_caps` parses an immutable conventional PCI capability
snapshot with a bounded, aligned, cycle-detecting traversal. DEVICE_CFG and
64-bit SHM ranges are checked against separate physical BAR apertures and
kernel-authorized mapped grants before a CPU virtual address is returned.
Unknown capability types remain ignorable; duplicate SHM IDs, truncated known
records, arithmetic wrap, aperture escape, and grant escape fail closed. The
parser preserves common+notify-only 2D readiness without promoting Venus.

The kernel-side `pci_bar_window_resolver` is a pure MDSOC policy owner between
PCI aperture discovery and address-space mutation. It resolves only an exact
BDF/BAR request represented by one present function snapshot and one memory
aperture. It rejects I/O BARs, 64-bit upper DWORDs, duplicate/absent rows,
unassigned/zero apertures, empty ranges, escape, and arithmetic wrap while
returning the original aperture provenance. It performs no config I/O or page
mapping.

A future live syscall must feed this owner from a serialized PCI probe and
reserve a caller-owned device VMA. Device VMAs must use user/UC/NX permissions,
must not release MMIO pages to PMM during unmap, and must not be inherited by
fork/COW without independent authority. Existing syscall 83 cannot satisfy
these invariants because it accepts caller-provided physical addresses and
checks a fixed capability tuple; it remains compatibility-only.

Device address-space ownership is now explicit through `VMA_DEVICE` and the
`vmm_device` policy owner. A detached device leaf never releases a PMM
reference. Any registered device VMA blocks COW cloning, while lifecycle-owned
BAR and DMA resources independently block fork and exec. This second gate is
required because compatibility MapBar predates VMA registration and DMA has a
separate allocation registry. Notification and IRQ handles remain inheritable;
unknown future resource kinds fail closed.

Compatibility MapBar now supplies USER|WRITABLE|UC|NX leaves, rolls back an
incomplete mapping, and records `RES_BAR_MAPPING` so exit can detach MMIO
without freeing its physical aperture. It still maps the active address space
from caller-provided physical coordinates and is not the production Venus
path. Syscall 88 must use an explicit `ProcessVmSpace`, collision preflight,
device-VMA reservation, exact BDF/BAR authority, and dedicated unmap/resource
retirement.

Promotion to `VirtioGpuVenusAdapter` remains blocked on all of the following:

1. negotiated virtio-gpu blob-resource and context-init support;
2. Venus capset retrieval and a compatible guest ICD;
3. guest shared-memory/blob mapping with cache and lifetime ownership;
4. a live controlq adapter, context/resource attachment, and real 3D command
   submission;
5. interrupt or polling completion with correlated fence identity;
6. device-origin readback and exact CPU-oracle parity; and
7. a QEMU/virglrenderer environment that demonstrably exposes the required path.

Unit tests may prove protocol admission without hardware. Environment evidence
must separately identify QEMU, virtio-gpu and virglrenderer versions, negotiated
features/capset, guest ICD identity, submission/fence IDs, and readback origin.
Until that environment evidence passes, the direct guest-native row remains a
blocker even if every protocol unit test is green.

## UNO Q

The adapter ladder is:

1. board identity and supplied Debian boot;
2. Turnip enumeration and canonical fixture submission;
3. fence completion and device-origin readback parity;
4. audited extraction of required MSM/device/layout/IR3 knowledge;
5. SimpleOS firmware, MMU/cache, queue, fence, readback, and display owners;
6. SimpleOS-native execution of the same fixture.

Mesa code is not copied wholesale. Reused code/data must carry upstream path,
commit/version, license, local adaptation, and verification provenance.

## Knowledge selection

The registry uses stable IDs and ordered entries. Selection is exact and
fail-closed:

1. exact feature lookup;
2. feature-group base, then exact expert;
3. longest-prefix layer match for every planned/changed path;
4. layer-base, then declared experts;
5. MDSOC-only override for kernel/drivers;
6. stable-ID deduplication and lexical ordering within each class;
7. content-hash receipt persisted under `.spipe/<slug>/`.

Claude, Codex, and Gemini compare the same receipt at handoff. A changed hash,
new source layer, ambiguous prefix, or missing entry invalidates the receipt.

## MDSOC ownership

- Common ProcessingIR contract: shared tree-node capability owner.
- QEMU/Adreno/CUDA adapters: private platform leaves behind ports.
- Session selection/evidence: GPU bridge capsule policy owner.
- Knowledge registry/selector: LLM-process tooling capsule.
- Feature/layer documents: immutable knowledge inputs, not runtime policy code.

No sibling adapter imports another sibling. Public-to-next-layer calls flow
through the two ports.
